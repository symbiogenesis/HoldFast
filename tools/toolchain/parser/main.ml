(* SPDX-License-Identifier: Apache-2.0 *)
(* Read one bounded UTF-8 source from stdin and emit a JSON syntax tree or diagnostic. *)

let read_source () =
  let bytes = Bytes.create (Ast.max_source_bytes + 1) in
  let rec read count =
    if count = Bytes.length bytes then count
    else
      let got = input stdin bytes count (Bytes.length bytes - count) in
      if got = 0 then count else read (count + got)
  in
  let count = read 0 in
  if count > Ast.max_source_bytes then
    raise (Ast.Refusal ("limit", 0, "source exceeds 65536 bytes"));
  Bytes.sub_string bytes 0 count

let is_forbidden_codepoint cp =
  (cp < 0x20 && cp <> 0x09 && cp <> 0x0a && cp <> 0x0d)
  || cp = 0x7f
  || (cp >= 0x200b && cp <= 0x200f)
  || (cp >= 0x202a && cp <= 0x202e)
  || cp = 0x2060
  || (cp >= 0x2066 && cp <= 0x2069)
  || cp = 0xfeff
  || cp = 0xfffd

let validate_utf8 source =
  if String.starts_with ~prefix:"\xEF\xBB\xBF" source then
    raise (Ast.Refusal ("encoding", 0, "remove the initial UTF-8 byte-order mark"));
  let length = String.length source in
  let byte index = Char.code source.[index] in
  let continuation index = index < length && byte index >= 0x80 && byte index <= 0xbf in
  let invalid index = raise (Ast.Refusal ("encoding", index, "source is not valid UTF-8")) in
  let rec walk index =
    if index < length then begin
      let lead = byte index in
      let width =
        if lead <= 0x7f then 1
        else if lead >= 0xc2 && lead <= 0xdf then 2
        else if lead >= 0xe0 && lead <= 0xef then 3
        else if lead >= 0xf0 && lead <= 0xf4 then 4
        else invalid index
      in
      if index + width > length then invalid index;
      for offset = 1 to width - 1 do
        if not (continuation (index + offset)) then invalid index
      done;
      if width >= 3 then begin
        let second = byte (index + 1) in
        if (lead = 0xe0 && second < 0xa0) || (lead = 0xed && second >= 0xa0)
           || (lead = 0xf0 && second < 0x90) || (lead = 0xf4 && second >= 0x90)
        then invalid index
      end;
      let cp =
        match width with
        | 1 -> lead
        | 2 -> ((lead land 0x1f) lsl 6) lor (byte (index + 1) land 0x3f)
        | 3 ->
            ((lead land 0x0f) lsl 12)
            lor ((byte (index + 1) land 0x3f) lsl 6)
            lor (byte (index + 2) land 0x3f)
        | _ ->
            ((lead land 0x07) lsl 18)
            lor ((byte (index + 1) land 0x3f) lsl 12)
            lor ((byte (index + 2) land 0x3f) lsl 6)
            lor (byte (index + 3) land 0x3f)
      in
      if is_forbidden_codepoint cp then
        raise (Ast.Refusal ("encoding", index,
          Printf.sprintf "source contains forbidden control or formatting character U+%04X" cp));
      walk (index + width)
    end
  in
  walk 0

let position source target =
  let limit = min target (String.length source) in
  let rec scan index line column =
    if index >= limit then (line, column)
    else match source.[index] with
      | '\r' ->
          let width = if index + 1 < limit && source.[index + 1] = '\n' then 2 else 1 in
          scan (index + width) (line + 1) 1
      | '\n' -> scan (index + 1) (line + 1) 1
      | character when Char.code character land 0xc0 = 0x80 ->
          scan (index + 1) line column
      | _ -> scan (index + 1) line (column + 1)
  in
  scan 0 1 1

let diagnostic source kind offset message =
  let line, column = position source offset in
  Ast.Object [("kind", Ast.String kind); ("line", Ast.Number line);
              ("column", Ast.Number column); ("message", Ast.String message)]

let classify_pure_failure state lexbuf default_offset history =
  let next_is_equal () =
    try Lexer.token state lexbuf = Parser.EQUAL
    with _ -> false
  in
  match history with
  | (curr_pos, Parser.CONST) :: (_, Parser.CONST) :: (_, Parser.PUBLIC) :: _ ->
      ("syntax", curr_pos, "repeated const declaration modifier")
  | (curr_pos, Parser.CONST) :: (_, Parser.CONST) :: _ ->
      ("syntax", curr_pos, "repeated const parameter qualifier")
  | (_, Parser.IDENT _) :: (type_pos, Parser.IDENT type_name) :: _ ->
      ("unsupported", type_pos, "type '" ^ type_name ^ "' is outside Nat and bool")
  | (type_pos, Parser.IDENT type_name) :: (_, (Parser.PUBLIC | Parser.LPAREN | Parser.COMMA)) :: _ ->
      ("unsupported", type_pos, "type '" ^ type_name ^ "' is outside Nat and bool")
  | (type_pos, Parser.IDENT type_name) :: (_, Parser.CONST) :: _ ->
      if next_is_equal () then
        ("syntax", type_pos, "const requires an explicit type before its name")
      else
        ("unsupported", type_pos, "type '" ^ type_name ^ "' is outside Nat and bool")
  | _ ->
      ("syntax", default_offset, "unexpected token or incomplete input")

let parse_one ~surface ~layout source =
  let current = ref 0 in
  let history = ref [] in
  let state_ref = ref None in
  let lexbuf_ref = ref None in
  let fail kind offset message =
    (1, Ast.encode (diagnostic source kind offset message))
  in
  try
    validate_utf8 source;
    let lexbuf = Lexing.from_string source in
    let state = Lexer.create ~surface () in
    state_ref := Some state;
    lexbuf_ref := Some lexbuf;
    let tokens = ref [] in
    let next lexbuf =
      let token = Lexer.token state lexbuf in
      let start_pos = Lexing.lexeme_start lexbuf in
      current := start_pos;
      if layout && token <> Parser.EOF then
        tokens := Ast.offsets (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) :: !tokens;
      if not surface then history := (start_pos, token) :: !history;
      token
    in
    let syntax = (if surface then Parser.surface_file else Parser.file) next lexbuf in
    let fields = [("schema", Ast.Number (if surface then 2 else 1)); ("ast", syntax.syntax)] in
    let fields = if layout then ("tokens", Ast.Array (List.rev !tokens)) :: fields else fields in
    (0, Ast.encode (Ast.Object fields))
  with
  | Ast.Refusal (kind, offset, message) -> fail kind offset message
  | Parser.Error ->
      (match surface, !state_ref, !lexbuf_ref with
       | false, Some state, Some lexbuf ->
           let kind, offset, message = classify_pure_failure state lexbuf !current !history in
           fail kind offset message
       | _ ->
           fail "syntax" !current "unexpected token or incomplete input")
  | Stack_overflow -> fail "limit" !current "native parser stack limit exceeded"
  | Sys_error message -> fail "io" !current message

let run_single ~surface ~layout =
  let source = ref "" in
  try
    source := read_source ();
    let code, payload = parse_one ~surface ~layout !source in
    print_endline payload;
    if code <> 0 then exit code
  with
  | Ast.Refusal (kind, offset, message) ->
      print_endline (Ast.encode (diagnostic !source kind offset message));
      exit 1
  | Sys_error message ->
      print_endline (Ast.encode (diagnostic !source "io" 0 message));
      exit 1

let run_batch () =
  try
    while true do
      let header = String.trim (input_line stdin) in
      let mode, count_str =
        match String.index_opt header ' ' with
        | Some idx ->
            (String.sub header 0 idx,
             String.trim (String.sub header (idx + 1) (String.length header - idx - 1)))
        | None -> ("", "")
      in
      let mode_flags =
        match mode with
        | "pure" -> Some (false, false)
        | "surface" -> Some (true, false)
        | "surface-layout" -> Some (true, true)
        | _ -> None
      in
      let count =
        match int_of_string_opt count_str with
        | Some n -> n
        | None -> -1
      in
      match mode_flags with
      | Some (surface, layout) when count >= 0 && count <= Ast.max_source_bytes ->
          let source = really_input_string stdin count in
          let code, payload = parse_one ~surface ~layout source in
          output_string stdout (string_of_int code ^ " " ^ payload ^ "\n");
          flush stdout
      | Some _ ->
          let payload = Ast.encode (diagnostic "" "limit" 0 "source exceeds 65536 bytes") in
          output_string stdout ("1 " ^ payload ^ "\n");
          flush stdout;
          raise End_of_file
      | None ->
          let payload = Ast.encode (diagnostic "" "syntax" 0 "invalid batch request header") in
          output_string stdout ("1 " ^ payload ^ "\n");
          flush stdout;
          raise End_of_file
    done
  with End_of_file -> ()

let () =
  set_binary_mode_in stdin true;
  set_binary_mode_out stdout true;
  match Array.to_list Sys.argv with
  | [_] -> run_single ~surface:false ~layout:false
  | [_; "--surface"] -> run_single ~surface:true ~layout:false
  | [_; "--surface-layout"] -> run_single ~surface:true ~layout:true
  | [_; "--batch"] -> run_batch ()
  | _ ->
      print_endline (Ast.encode (diagnostic "" "syntax" 0 "expected no arguments, --surface or --surface-layout"));
      exit 1
