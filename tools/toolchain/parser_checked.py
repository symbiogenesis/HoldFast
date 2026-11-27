# SPDX-License-Identifier: Apache-2.0
"""Build, qualify, and run the Rocq-extracted pure parser.

See the [parser contract](../../docs/tooling/parser.md) for the grammar, proof,
extraction, and runtime checks.
"""

import atexit
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePosixPath
from typing import cast

from toolchain import (
    env,
    migration,
    proofenv,
)
from toolchain import (
    parser as holdfast_parser,
)
from toolchain._isolated_worker import (
    close_worker_proc as _close_proc,
)
from toolchain._isolated_worker import (
    parse_batch_reply_line,
)
from toolchain.ast import source_text
from toolchain.atomic import atomic_path, publish_report
from toolchain.hashing import file_sha256, read_bounded
from toolchain.hashing import sha256_bytes as _sha256

RELEASE = "20260209"
ARCHIVE_SHA512 = (
    "aafad186f328ae8dd4cc69af0f30c1a0b208cf5148a7a94c150099be03838503c5ec1"
    "2918de26cd7f794b5a72f114bc1bae8d81058bd0ea10372a3b06818687e"
)
ARCHIVE_URL = f"https://opam.ocaml.org/cache/sha512/aa/{ARCHIVE_SHA512}"
UPSTREAM_REPAIR = "6dedce5de5df8f139c42326f3bd95e7a1c878674"
INTERPRETER_SHA256 = "4891ad9d65843fefa4d9d424e0d065e241760f705464efc233796d445b16294f"
CANDIDATE_SHA256 = "69cfbdd086858ef37fa50eed10866379a51bd858113a9716331d88f9e46e7fde"
REFERENCE_SHA256 = "04aa7bda193a67219fea99ee6f1b86eb7db3da735b04e32f662ac1e5c041b02c"
VALIDATOR_COMPLETE_SHA256 = "c7e1f4f25be2a4371d06dd1d01ea2adb21d889c1c18739ebf74afca8408b4f64"
VALIDATOR_COMPLETE_CANDIDATE_SHA256 = "1a284ece0e5b547e2b816c0f7623ee1ee628d30385f5d3dde4dd1a180589cb66"
VERSION_SHA256 = "3746feeefa899fe0d43e4db0ec53f2d7ddd72076d9fab29cdcc9ecb0250072e6"
LICENSES = {
    "LICENSE": "9c97527b92b577647880abd2a5eaf5bf0f3b3df1bd09d9f93fc4e103eb1d30d5",
    "coq-menhirlib/LICENSE": "218c42550a9b4ff6e48bf38218908755fe156b2e5c586531c2eb8893248a102d",
}
MODULES = (
    "Alphabet", "Automaton", "Grammar", "Interpreter", "Interpreter_complete",
    "Interpreter_correct", "Main", "Validator_classes", "Validator_complete",
    "Validator_safe", "Version",
)
GRAMMAR_MODULES = ("HoldFastPureAst", "HoldFastPureGrammar", "HoldFastPureProofs")
ALL_MODULES = (*MODULES, *GRAMMAR_MODULES)
TARGETS = ("pop", "reduce_step", "parse")
THEOREMS = (
    "holdfast_file_safe",
    "holdfast_file_complete_validator",
    "holdfast_file_correct",
    "holdfast_file_complete",
    "holdfast_file_unambiguity",
    "holdfast_file_positive_precedence",
    "holdfast_file_bare_local_refused",
    "holdfast_file_empty_module_rejected",
    "holdfast_file_zero_fuel_timeout",
)
PURE_TERMINALS: tuple[str, ...] = (
    "MODULE", "PUBLIC", "NAT", "BOOL", "LET", "CONST", "RETURN", "IF", "ELSE", "TRUE", "FALSE",
    "LPAREN", "RPAREN", "LBRACE", "RBRACE", "SEMICOLON", "COMMA", "COLON", "DOT", "FATARROW",
    "EQUAL", "PLUS", "MINUS", "STAR", "SLASH", "PERCENT",
    "EQ", "LE", "NE", "LT", "GT", "GE", "AND", "OR", "NOT", "EOF",
    "IDENT", "DECIMAL",
)
EXPECTED_PURE_SKELETON: dict[str, tuple[tuple[str, ...], ...]] = {
    "file": (("MODULE", "name", "SEMICOLON", "nonempty_list(pure_declaration)", "EOF"),),
    "pure_declaration": (
        ("PUBLIC", "ioption(CONST)", "value_type", "name", "LPAREN", "comma_list(parameter)", "RPAREN", "function_body"),
        ("PUBLIC", "CONST", "value_type", "name", "EQUAL", "expression", "SEMICOLON"),
    ),
    "name": (("IDENT",),),
    "value_type": (("NAT",), ("BOOL",)),
    "function_body": (("block",), ("FATARROW", "expression", "SEMICOLON")),
    "parameter": (("option(CONST)", "value_type", "name"),),
    "block": (("LBRACE", "list(binding)", "exit", "RBRACE"),),
    "binding": (
        ("LET", "name", "EQUAL", "expression", "SEMICOLON"),
        ("LET", "value_type", "name", "EQUAL", "expression", "SEMICOLON"),
        ("value_type", "name", "EQUAL", "expression", "SEMICOLON"),
        ("name", "EQUAL", "expression", "SEMICOLON"),
        ("CONST", "value_type", "name", "EQUAL", "expression", "SEMICOLON"),
    ),
    "exit": (
        ("RETURN", "expression", "SEMICOLON"),
        ("IF", "LPAREN", "expression", "RPAREN", "block", "ELSE", "block"),
    ),
    "expression": (("left_binary(conjunction,s_disjunction_operator)",),),
    "conjunction": (("left_binary(comparison,s_conjunction_operator)",),),
    "comparison": (("sum",), ("sum", "comparison_operator", "sum")),
    "comparison_operator": (("EQ",), ("LE",), ("NE",), ("LT",), ("GT",), ("GE",)),
    "sum": (("left_binary(product,s_sum_operator)",),),
    "plus_operator": (("PLUS",),),
    "product": (("left_binary(unary,s_product_operator)",),),
    "star_operator": (("STAR",),),
    "unary": (("atom",), ("negation_operator", "unary")),
    "negation_operator": (("NOT",),),
    "atom": (
        ("DECIMAL",), ("TRUE",), ("FALSE",), ("name",),
        ("name", "LPAREN", "comma_list(call_argument(expression,name))", "RPAREN"),
        ("NAT", "DOT", "name", "LPAREN", "comma_list(call_argument(expression,name))", "RPAREN"),
        ("LPAREN", "expression", "RPAREN"),
    ),
    "call_argument(expression,identifier)": (
        ("expression",),
        ("identifier", "COLON", "expression"),
    ),
    "left_binary(operand,operator)": (
        ("operand",),
        ("left_binary(operand,operator)", "operator", "operand"),
    ),
    "s_disjunction_operator": (("OR",),),
    "s_conjunction_operator": (("AND",),),
    "s_sum_operator": (("plus_operator",), ("MINUS",)),
    "s_product_operator": (("star_operator",), ("SLASH",), ("PERCENT",)),
    "comma_list(item)": ((), ("comma_nonempty_list(item)",)),
    "comma_nonempty_list(item)": (("item", "comma_tail(item)"),),
    "comma_tail(item)": ((), ("COMMA",), ("COMMA", "item", "comma_tail(item)")),
}
MAX_ARCHIVE_BYTES = 32 * 1024 * 1024
TIMEOUT = 180

FROZEN_QUERY = """From MenhirLib Require Import Automaton Interpreter Validator_complete.
Set Printing All.
Set Printing Universes.
Set Printing Depth 1000000.
Set Printing Width 1000000.
Module Probe (A: Automaton.T).
Module I := Interpreter.Make A.
Module V := Validator_complete.Make A.
Check I.pop.
Print I.pop.
Print Assumptions I.pop.
Check I.reduce_step.
Print I.reduce_step.
Print Assumptions I.reduce_step.
Check I.parse.
Print I.parse.
Print Assumptions I.parse.
Check V.is_validator_forall_items.
Print Assumptions V.is_validator_forall_items.
Check V.complete_is_validator.
Print Assumptions V.complete_is_validator.
End Probe.
"""
ASSUMPTIONS_QUERY = """From MenhirLib Require Import Automaton Main.
Module SupportBoundary (Aut : Automaton.T).
Module Parser := Main.Make Aut.
Print Assumptions Parser.parse_correct.
Print Assumptions Parser.parse_complete.
Print Assumptions Parser.unambiguity.
End SupportBoundary.
"""

HOLDFAST_PURE_AST_V = """(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Bool Arith List Ascii String.
Import ListNotations.
Open Scope string_scope.

Definition span : Type := (nat * nat)%type.

Inductive json : Type :=
| JNull : json
| JBoolean : bool -> json
| JNumber : nat -> json
| JString : string -> json
| JArray : list json -> json
| JObject : list (string * json) -> json.

Record located_text : Type := {
  loc_span : span;
  loc_value : string
}.

Record node : Type := {
  node_span : span;
  node_depth : nat;
  node_syntax : json
}.

Inductive outcome (A : Type) : Type :=
| Accepted : A -> outcome A
| Refused : string -> nat -> string -> outcome A.
Arguments Accepted {A} _.
Arguments Refused {A} _ _ _.

Definition max_syntax_depth : nat := 256.
Definition max_block_bindings : nat := 64.

Definition span_json (sp : span) : json :=
  JArray [JNumber (fst sp); JNumber (snd sp)].

Definition loc_text (sp : span) (value : string) : located_text :=
  {| loc_span := sp; loc_value := value |}.

Definition loc_json (item : located_text) : json :=
  JObject [("text", JString (loc_value item)); ("span", span_json (loc_span item))].

Definition loc_start (item : located_text) : nat := fst (loc_span item).
Definition loc_end (item : located_text) : nat := snd (loc_span item).
Definition node_start (item : node) : nat := fst (node_span item).
Definition node_end (item : node) : nat := snd (node_span item).

Fixpoint max_depth (items : list node) : nat :=
  match items with
  | [] => 0
  | item :: rest => Nat.max (node_depth item) (max_depth rest)
  end.

Definition make_node (kind : string) (first_pos last_pos : nat)
  (fields : list (string * json)) (children : list node) : outcome node :=
  let depth := S (max_depth children) in
  if Nat.ltb max_syntax_depth depth then
    Refused "limit" first_pos "syntax tree exceeds depth 256"
  else
    Accepted {|
      node_span := (first_pos, last_pos);
      node_depth := depth;
      node_syntax := JObject (("kind", JString kind) :: ("span", span_json (first_pos, last_pos)) :: fields)
    |}.

Definition array_json (items : list node) : json :=
  JArray (List.map node_syntax items).

Definition const_fields (flag : option span) : list (string * json) :=
  match flag with
  | None => []
  | Some _ => [("const", JBoolean true)]
  end.

Definition bind {A B : Type} (value : outcome A) (next : A -> outcome B) : outcome B :=
  match value with
  | Accepted item => next item
  | Refused kind offset message => Refused kind offset message
  end.

Fixpoint sequence_outcomes {A : Type} (items : list (outcome A)) : outcome (list A) :=
  match items with
  | [] => Accepted []
  | item :: rest =>
      bind item (fun head =>
      bind (sequence_outcomes rest) (fun tail =>
      Accepted (head :: tail)))
  end.

Fixpoint last_end (fallback : nat) (items : list node) : nat :=
  match items with
  | [] => fallback
  | [item] => node_end item
  | _ :: rest => last_end fallback rest
  end.

Definition binary_node (op : located_text) (left_out right_out : outcome node) : outcome node :=
  bind left_out (fun left_node =>
  bind right_out (fun right_node =>
  make_node "binary" (node_start left_node) (node_end right_node)
    [("operator", loc_json op); ("left", node_syntax left_node); ("right", node_syntax right_node)]
    [left_node; right_node])).
"""

HOLDFAST_PURE_GRAMMAR_MLY = """/* SPDX-License-Identifier: Apache-2.0 */
%{
From Stdlib Require Import Bool Arith List String.
From MenhirLib Require Import HoldFastPureAst.
Import ListNotations.
Open Scope string_scope.
%}

%token <HoldFastPureAst.span> MODULE PUBLIC NAT BOOL LET CONST RETURN IF ELSE TRUE FALSE
%token <HoldFastPureAst.span> LPAREN RPAREN LBRACE RBRACE SEMICOLON COMMA COLON DOT FATARROW
%token <HoldFastPureAst.span> EQUAL PLUS MINUS STAR SLASH PERCENT
%token <HoldFastPureAst.span> EQ LE NE LT GT GE AND OR NOT EOF
%token <HoldFastPureAst.span * String.string> IDENT DECIMAL

%start <HoldFastPureAst.outcome HoldFastPureAst.node> file
%type <HoldFastPureAst.outcome HoldFastPureAst.node> pure_declaration value_type function_body parameter
%type <HoldFastPureAst.outcome HoldFastPureAst.node> block binding exit expression conjunction comparison
%type <HoldFastPureAst.outcome HoldFastPureAst.node> sum product unary atom
%type <HoldFastPureAst.outcome HoldFastPureAst.node> call_argument(expression, name)
%type <HoldFastPureAst.outcome HoldFastPureAst.node> left_binary(conjunction, s_disjunction_operator)
%type <HoldFastPureAst.outcome HoldFastPureAst.node> left_binary(comparison, s_conjunction_operator)
%type <HoldFastPureAst.outcome HoldFastPureAst.node> left_binary(product, s_sum_operator)
%type <HoldFastPureAst.outcome HoldFastPureAst.node> left_binary(unary, s_product_operator)
%type <HoldFastPureAst.located_text> name comparison_operator plus_operator star_operator
%type <HoldFastPureAst.located_text> negation_operator s_disjunction_operator s_conjunction_operator
%type <HoldFastPureAst.located_text> s_sum_operator s_product_operator
%type <Datatypes.option HoldFastPureAst.span> option(CONST)
%type <Datatypes.list (HoldFastPureAst.outcome HoldFastPureAst.node)> list(binding) nonempty_list(pure_declaration)
%type <Datatypes.list (HoldFastPureAst.outcome HoldFastPureAst.node)> comma_list(parameter) comma_nonempty_list(parameter) comma_tail(parameter)
%type <Datatypes.list (HoldFastPureAst.outcome HoldFastPureAst.node)> comma_list(call_argument(expression, name)) comma_nonempty_list(call_argument(expression, name)) comma_tail(call_argument(expression, name))

%%

option(X):
  { (@None _) }
| x=X
  { Some x }

list(X):
  { (@nil _) }
| x=X xs=list(X)
  { cons x xs }

nonempty_list(X):
  x=X
  { cons x nil }
| x=X xs=nonempty_list(X)
  { cons x xs }

file:
  m=MODULE module_name=name s=SEMICOLON declarations=nonempty_list(pure_declaration) EOF
    { bind (sequence_outcomes declarations) (fun decl_nodes =>
      make_node "file" (fst m) (last_end (snd s) decl_nodes)
        [("name", loc_json module_name); ("declarations", array_json decl_nodes)]
        decl_nodes) }

pure_declaration:
  p=PUBLIC result=value_type function_name=name LPAREN
  parameters=comma_list(parameter) RPAREN body=function_body
    { bind result (fun result_node =>
      bind (sequence_outcomes parameters) (fun param_nodes =>
      bind body (fun body_node =>
      make_node "function" (fst p) (node_end body_node)
        ([("name", loc_json function_name); ("result", node_syntax result_node);
          ("parameters", array_json param_nodes); ("body", node_syntax body_node)]
         ++ const_fields None)
        (result_node :: body_node :: param_nodes)))) }
| p=PUBLIC c=CONST result=value_type function_name=name LPAREN
  parameters=comma_list(parameter) RPAREN body=function_body
    { bind result (fun result_node =>
      bind (sequence_outcomes parameters) (fun param_nodes =>
      bind body (fun body_node =>
      make_node "function" (fst p) (node_end body_node)
        ([("name", loc_json function_name); ("result", node_syntax result_node);
          ("parameters", array_json param_nodes); ("body", node_syntax body_node)]
         ++ const_fields (Some c))
        (result_node :: body_node :: param_nodes)))) }
| p=PUBLIC CONST vtype=value_type constant_name=name EQUAL value=expression s=SEMICOLON
    { bind vtype (fun type_node =>
      bind value (fun value_node =>
      make_node "constant" (fst p) (snd s)
        [("name", loc_json constant_name); ("type", node_syntax type_node);
         ("value", node_syntax value_node)]
        [type_node; value_node])) }

name:
  spelling=IDENT
    { loc_text (fst spelling) (snd spelling) }

value_type:
  sp=NAT
    { make_node "type" (fst sp) (snd sp) [("name", JString "Nat")] [] }
| sp=BOOL
    { make_node "type" (fst sp) (snd sp) [("name", JString "bool")] [] }

function_body:
  value=block
    { value }
| arrow=FATARROW value=expression s=SEMICOLON
    { bind value (fun value_node =>
      make_node "expression_body" (fst arrow) (snd s)
        [("value", node_syntax value_node)] [value_node]) }

parameter:
  constant=option(CONST) parameter_type=value_type parameter_name=name
    { bind parameter_type (fun type_node =>
      let first_pos := match constant with
                       | Some sp => fst sp
                       | None => node_start type_node
                       end in
      make_node "parameter" first_pos (loc_end parameter_name)
        ([("name", loc_json parameter_name); ("type", node_syntax type_node)]
         ++ const_fields constant)
        [type_node]) }

block:
  open_b=LBRACE bindings=list(binding) terminal=exit close_b=RBRACE
    { bind (sequence_outcomes bindings) (fun binding_nodes =>
      bind terminal (fun terminal_node =>
      if Nat.ltb max_block_bindings (List.length binding_nodes) then
        Refused "limit" (fst open_b) "block exceeds 64 bindings"
      else
        make_node "block" (fst open_b) (snd close_b)
          [("bindings", array_json binding_nodes); ("exit", node_syntax terminal_node)]
          (terminal_node :: binding_nodes))) }

binding:
  kw=LET binding_name=name EQUAL value=expression s=SEMICOLON
    { bind value (fun value_node =>
      make_node "let" (fst kw) (snd s)
        [("name", loc_json binding_name); ("value", node_syntax value_node)]
        [value_node]) }
| kw=LET annotation=value_type binding_name=name EQUAL value=expression s=SEMICOLON
    { bind annotation (fun type_node =>
      bind value (fun value_node =>
      make_node "let" (fst kw) (snd s)
        [("name", loc_json binding_name); ("type", node_syntax type_node);
         ("value", node_syntax value_node)]
        [type_node; value_node])) }
| annotation=value_type binding_name=name EQUAL value=expression SEMICOLON
    { bind annotation (fun type_node =>
      bind value (fun _ =>
      let _ := binding_name in
      Refused "syntax" (node_start type_node)
        "local declaration requires 'let' or 'var' before its type (write 'let T x = e;' or 'var T x = e;')")) }
| binding_name=name EQUAL value=expression s=SEMICOLON
    { bind value (fun value_node =>
      make_node "reassignment" (loc_start binding_name) (snd s)
        [("name", loc_json binding_name); ("value", node_syntax value_node)]
        [value_node]) }
| kw=CONST vtype=value_type constant_name=name EQUAL value=expression s=SEMICOLON
    { bind vtype (fun type_node =>
      bind value (fun value_node =>
      make_node "constant_local" (fst kw) (snd s)
        [("name", loc_json constant_name); ("type", node_syntax type_node);
         ("value", node_syntax value_node)]
        [type_node; value_node])) }

exit:
  kw=RETURN value=expression s=SEMICOLON
    { bind value (fun value_node =>
      make_node "return" (fst kw) (snd s)
        [("value", node_syntax value_node)] [value_node]) }
| kw=IF LPAREN condition=expression RPAREN yes=block ELSE no=block
    { bind condition (fun cond_node =>
      bind yes (fun yes_node =>
      bind no (fun no_node =>
      make_node "if" (fst kw) (node_end no_node)
        [("condition", node_syntax cond_node); ("then", node_syntax yes_node);
         ("else", node_syntax no_node)]
        [cond_node; yes_node; no_node]))) }

expression:
  value=left_binary(conjunction, s_disjunction_operator)
    { value }

conjunction:
  value=left_binary(comparison, s_conjunction_operator)
    { value }

comparison:
  value=sum
    { value }
| left=sum op=comparison_operator right=sum
    { binary_node op left right }

comparison_operator:
  sp=EQ { loc_text sp "==" }
| sp=LE { loc_text sp "<=" }
| sp=NE { loc_text sp "!=" }
| sp=LT { loc_text sp "<" }
| sp=GT { loc_text sp ">" }
| sp=GE { loc_text sp ">=" }

sum:
  value=left_binary(product, s_sum_operator)
    { value }

plus_operator:
  sp=PLUS { loc_text sp "+" }

product:
  value=left_binary(unary, s_product_operator)
    { value }

star_operator:
  sp=STAR { loc_text sp "*" }

unary:
  value=atom
    { value }
| operator=negation_operator value=unary
    { bind value (fun value_node =>
      make_node "unary" (loc_start operator) (node_end value_node)
        [("operator", loc_json operator); ("value", node_syntax value_node)]
        [value_node]) }

negation_operator:
  sp=NOT { loc_text sp "!" }

atom:
  value=DECIMAL
    { make_node "nat" (fst (fst value)) (snd (fst value))
        [("value", JString (snd value))] [] }
| sp=TRUE
    { make_node "bool" (fst sp) (snd sp) [("value", JBoolean true)] [] }
| sp=FALSE
    { make_node "bool" (fst sp) (snd sp) [("value", JBoolean false)] [] }
| value=name
    { make_node "name" (loc_start value) (loc_end value)
        [("name", loc_json value)] [] }
| callee=name LPAREN arguments=comma_list(call_argument(expression, name)) close_p=RPAREN
    { bind (sequence_outcomes arguments) (fun arg_nodes =>
      make_node "call" (loc_start callee) (snd close_p)
        [("callee", loc_json callee); ("arguments", array_json arg_nodes)]
        arg_nodes) }
| qualifier=NAT DOT callee=name LPAREN arguments=comma_list(call_argument(expression, name)) close_p=RPAREN
    { bind (sequence_outcomes arguments) (fun arg_nodes =>
      make_node "call" (fst qualifier) (snd close_p)
        [("qualifier", loc_json (loc_text qualifier "Nat")); ("callee", loc_json callee);
         ("arguments", array_json arg_nodes)]
        arg_nodes) }
| open_p=LPAREN value=expression close_p=RPAREN
    { bind value (fun value_node =>
      make_node "group" (fst open_p) (snd close_p)
        [("value", node_syntax value_node)] [value_node]) }

call_argument(expression, identifier):
  value=expression
    { bind value (fun value_node =>
      make_node "argument" (node_start value_node) (node_end value_node)
        [("label", JNull); ("value", node_syntax value_node)] [value_node]) }
| label=identifier COLON value=expression
    { bind value (fun value_node =>
      make_node "argument" (loc_start label) (node_end value_node)
        [("label", loc_json label); ("value", node_syntax value_node)] [value_node]) }

left_binary(operand, operator):
  value=operand
    { value }
| left=left_binary(operand, operator) op=operator right=operand
    { binary_node op left right }

s_disjunction_operator:
  sp=OR { loc_text sp "||" }

s_conjunction_operator:
  sp=AND { loc_text sp "&&" }

s_sum_operator:
  value=plus_operator { value }
| sp=MINUS { loc_text sp "-" }

s_product_operator:
  value=star_operator { value }
| sp=SLASH { loc_text sp "/" }
| sp=PERCENT { loc_text sp "%" }

comma_list(item):
  { (@nil _) }
| values=comma_nonempty_list(item) { values }

comma_nonempty_list(item):
  first=item rest=comma_tail(item) { cons first rest }

comma_tail(item):
  { (@nil _) }
| COMMA { (@nil _) }
| COMMA first=item rest=comma_tail(item) { cons first rest }
"""

HOLDFAST_PURE_PROOFS_V = """(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Bool Arith List String.
From MenhirLib Require Import HoldFastPureAst HoldFastPureGrammar.
Import ListNotations.
Import HoldFastPureGrammar.Gram HoldFastPureGrammar.Aut.GramDefs.
Open Scope string_scope.

Definition version_guard : unit := HoldFastPureGrammar.version_check.

Theorem holdfast_file_safe :
  HoldFastPureGrammar.MenhirLibParser.safe_validator tt = true.
Proof. exact HoldFastPureGrammar.safe. Qed.

Theorem holdfast_file_complete_validator :
  HoldFastPureGrammar.MenhirLibParser.complete_validator tt = true.
Proof. exact HoldFastPureGrammar.complete. Qed.

Theorem holdfast_file_correct :
  forall (log_fuel : nat) (buffer : HoldFastPureGrammar.MenhirLibParser.Inter.buffer),
  match HoldFastPureGrammar.file log_fuel buffer with
  | HoldFastPureGrammar.MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : parse_tree (NT file'nt) word),
        buffer = HoldFastPureGrammar.MenhirLibParser.Inter.app_buf word buffer_new /\\
        pt_sem tree = sem
  | _ => True
  end.
Proof. exact HoldFastPureGrammar.file_correct. Qed.

Theorem holdfast_file_complete :
  forall (log_fuel : nat) (word : list HoldFastPureGrammar.token) (buffer_end : HoldFastPureGrammar.MenhirLibParser.Inter.buffer)
         (tree : parse_tree (NT file'nt) word),
  match HoldFastPureGrammar.file log_fuel (HoldFastPureGrammar.MenhirLibParser.Inter.app_buf word buffer_end) with
  | HoldFastPureGrammar.MenhirLibParser.Inter.Fail_pr => False
  | HoldFastPureGrammar.MenhirLibParser.Inter.Parsed_pr output_res buffer_end_res =>
      output_res = pt_sem tree /\\
      buffer_end_res = buffer_end /\\ (pt_size tree <= PeanoNat.Nat.pow 2 log_fuel)%nat
  | HoldFastPureGrammar.MenhirLibParser.Inter.Timeout_pr =>
      (PeanoNat.Nat.pow 2 log_fuel < pt_size tree)%nat
  end.
Proof. exact HoldFastPureGrammar.file_complete. Qed.

Theorem holdfast_file_unambiguity :
  forall (word : list HoldFastPureGrammar.token)
         (tree1 tree2 : parse_tree (NT file'nt) word),
    pt_sem tree1 = pt_sem tree2.
Proof.
  exact (HoldFastPureGrammar.MenhirLibParser.unambiguity
           HoldFastPureGrammar.safe HoldFastPureGrammar.complete
           (inhabits (HoldFastPureGrammar.EOF (0, 0)))
           HoldFastPureGrammar.Aut.Init'0).
Qed.

CoFixpoint eof_buffer (sp : span) : HoldFastPureGrammar.MenhirLibParser.Inter.buffer :=
  HoldFastPureGrammar.MenhirLibParser.Inter.Buf_cons (HoldFastPureGrammar.EOF sp) (eof_buffer sp).

Definition token_stream (words : list HoldFastPureGrammar.token) (eof_span : span)
  : HoldFastPureGrammar.MenhirLibParser.Inter.buffer :=
  HoldFastPureGrammar.MenhirLibParser.Inter.app_buf words (eof_buffer eof_span).

Definition parse_tokens (log_fuel : nat) (words : list HoldFastPureGrammar.token) (eof_span : span)
  : option (outcome node) :=
  match HoldFastPureGrammar.file log_fuel (token_stream words eof_span) with
  | HoldFastPureGrammar.MenhirLibParser.Inter.Parsed_pr result _ => Some result
  | _ => None
  end.

Definition sample_Precedence_tokens : list HoldFastPureGrammar.token := [
  HoldFastPureGrammar.MODULE (0, 6);
  HoldFastPureGrammar.IDENT ((7, 8), "M");
  HoldFastPureGrammar.SEMICOLON (8, 9);
  HoldFastPureGrammar.PUBLIC (10, 16);
  HoldFastPureGrammar.NAT (17, 20);
  HoldFastPureGrammar.IDENT ((21, 22), "F");
  HoldFastPureGrammar.LPAREN (22, 23);
  HoldFastPureGrammar.RPAREN (23, 24);
  HoldFastPureGrammar.LBRACE (25, 26);
  HoldFastPureGrammar.RETURN (27, 33);
  HoldFastPureGrammar.DECIMAL ((34, 35), "1");
  HoldFastPureGrammar.PLUS (36, 37);
  HoldFastPureGrammar.DECIMAL ((38, 39), "2");
  HoldFastPureGrammar.STAR (40, 41);
  HoldFastPureGrammar.DECIMAL ((42, 43), "3");
  HoldFastPureGrammar.SEMICOLON (43, 44);
  HoldFastPureGrammar.RBRACE (45, 46);
  HoldFastPureGrammar.EOF (46, 46)
].

Definition sample_BareLocal_tokens : list HoldFastPureGrammar.token := [
  HoldFastPureGrammar.MODULE (0, 6);
  HoldFastPureGrammar.IDENT ((7, 8), "M");
  HoldFastPureGrammar.SEMICOLON (8, 9);
  HoldFastPureGrammar.PUBLIC (10, 16);
  HoldFastPureGrammar.NAT (17, 20);
  HoldFastPureGrammar.IDENT ((21, 22), "F");
  HoldFastPureGrammar.LPAREN (22, 23);
  HoldFastPureGrammar.RPAREN (23, 24);
  HoldFastPureGrammar.LBRACE (25, 26);
  HoldFastPureGrammar.NAT (27, 30);
  HoldFastPureGrammar.IDENT ((31, 32), "x");
  HoldFastPureGrammar.EQUAL (33, 34);
  HoldFastPureGrammar.DECIMAL ((35, 36), "1");
  HoldFastPureGrammar.SEMICOLON (36, 37);
  HoldFastPureGrammar.RETURN (38, 44);
  HoldFastPureGrammar.IDENT ((45, 46), "x");
  HoldFastPureGrammar.SEMICOLON (46, 47);
  HoldFastPureGrammar.RBRACE (48, 49);
  HoldFastPureGrammar.EOF (49, 49)
].

Definition sample_EmptyModule_tokens : list HoldFastPureGrammar.token := [
  HoldFastPureGrammar.MODULE (0, 6);
  HoldFastPureGrammar.IDENT ((7, 8), "M");
  HoldFastPureGrammar.SEMICOLON (8, 9);
  HoldFastPureGrammar.EOF (9, 9)
].

Theorem holdfast_file_positive_precedence :
  match parse_tokens 6 sample_Precedence_tokens (46, 46) with
  | Some (Accepted parsed) =>
      (Nat.eqb (fst (node_span parsed)) 0 &&
       Nat.eqb (snd (node_span parsed)) 46 &&
       Nat.eqb (node_depth parsed) 7)%bool
  | _ => false
  end = true.
Proof. lazy; reflexivity. Qed.

Theorem holdfast_file_bare_local_refused :
  parse_tokens 6 sample_BareLocal_tokens (49, 49) =
  Some (Refused "syntax" 27
    "local declaration requires 'let' or 'var' before its type (write 'let T x = e;' or 'var T x = e;')").
Proof. lazy; reflexivity. Qed.

Theorem holdfast_file_empty_module_rejected :
  parse_tokens 6 sample_EmptyModule_tokens (9, 9) = None.
Proof. lazy; reflexivity. Qed.

Theorem holdfast_file_zero_fuel_timeout :
  HoldFastPureGrammar.file 0 (token_stream sample_Precedence_tokens (46, 46)) =
  HoldFastPureGrammar.MenhirLibParser.Inter.Timeout_pr.
Proof. lazy; reflexivity. Qed.

Print Assumptions holdfast_file_safe.
Print Assumptions holdfast_file_complete_validator.
Print Assumptions holdfast_file_correct.
Print Assumptions holdfast_file_complete.
Print Assumptions holdfast_file_unambiguity.
Print Assumptions holdfast_file_positive_precedence.
Print Assumptions holdfast_file_bare_local_refused.
Print Assumptions holdfast_file_empty_module_rejected.
Print Assumptions holdfast_file_zero_fuel_timeout.
"""

HOLDFAST_PURE_EXTRACTION_V = """(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Extraction.
From MenhirLib Require Import HoldFastPureAst HoldFastPureGrammar HoldFastPureProofs.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "holdfast_checked_parser.ml" HoldFastPureGrammar.file.
"""

CHECKED_MAIN_ML = """(* SPDX-License-Identifier: Apache-2.0 *)
(* Execute the extracted Rocq pure parser over the shared UTF-8/lexer boundary. *)

let peano =
  let table = Array.make (Ast.max_source_bytes + 1) Holdfast_checked_parser.O in
  for i = 1 to Ast.max_source_bytes do
    table.(i) <- Holdfast_checked_parser.S table.(i - 1)
  done;
  table

let nat_of_int n =
  if n >= 0 && n <= Ast.max_source_bytes then peano.(n)
  else
    let rec loop acc k =
      if k <= 0 then acc
      else loop (Holdfast_checked_parser.S acc) (k - 1)
    in
    loop peano.(Ast.max_source_bytes) (n - Ast.max_source_bytes)

let int_of_nat n =
  let rec loop acc = function
    | Holdfast_checked_parser.O -> acc
    | Holdfast_checked_parser.S rest -> loop (acc + 1) rest
  in
  loop 0 n

let bit b = if b then Holdfast_checked_parser.True else Holdfast_checked_parser.False

let unbit = function
  | Holdfast_checked_parser.True -> 1
  | Holdfast_checked_parser.False -> 0

let ascii_of_char ch =
  let code = Char.code ch in
  Holdfast_checked_parser.Ascii (
    bit (code land 1 <> 0),
    bit (code land 2 <> 0),
    bit (code land 4 <> 0),
    bit (code land 8 <> 0),
    bit (code land 16 <> 0),
    bit (code land 32 <> 0),
    bit (code land 64 <> 0),
    bit (code land 128 <> 0)
  )

let char_of_ascii = function
  | Holdfast_checked_parser.Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
      Char.chr (
        unbit b0
        lor (unbit b1 lsl 1)
        lor (unbit b2 lsl 2)
        lor (unbit b3 lsl 3)
        lor (unbit b4 lsl 4)
        lor (unbit b5 lsl 5)
        lor (unbit b6 lsl 6)
        lor (unbit b7 lsl 7)
      )

let coq_string_of_string s =
  let rec loop idx acc =
    if idx < 0 then acc
    else loop (idx - 1) (Holdfast_checked_parser.String (ascii_of_char s.[idx], acc))
  in
  loop (String.length s - 1) Holdfast_checked_parser.EmptyString

let string_of_coq_string s =
  let buf = Buffer.create 32 in
  let rec loop = function
    | Holdfast_checked_parser.EmptyString -> Buffer.contents buf
    | Holdfast_checked_parser.String (ch, rest) ->
        Buffer.add_char buf (char_of_ascii ch);
        loop rest
  in
  loop s

let list_of_coq_list items =
  let rec loop acc = function
    | Holdfast_checked_parser.Nil -> List.rev acc
    | Holdfast_checked_parser.Cons (head, tail) -> loop (head :: acc) tail
  in
  loop [] items

let rec ast_json_of_coq_json = function
  | Holdfast_checked_parser.JNull -> Ast.Null
  | Holdfast_checked_parser.JBoolean Holdfast_checked_parser.True -> Ast.Boolean true
  | Holdfast_checked_parser.JBoolean Holdfast_checked_parser.False -> Ast.Boolean false
  | Holdfast_checked_parser.JNumber n -> Ast.Number (int_of_nat n)
  | Holdfast_checked_parser.JString s -> Ast.String (string_of_coq_string s)
  | Holdfast_checked_parser.JArray items ->
      Ast.Array (List.map ast_json_of_coq_json (list_of_coq_list items))
  | Holdfast_checked_parser.JObject fields ->
      Ast.Object (
        List.map
          (fun (Holdfast_checked_parser.Pair (k, v)) ->
            (string_of_coq_string k, ast_json_of_coq_json v))
          (list_of_coq_list fields)
      )

let coq_span start_pos end_pos =
  Holdfast_checked_parser.Pair (nat_of_int start_pos, nat_of_int end_pos)

let convert_token start_pos end_pos (raw : Parser.token) : Holdfast_checked_parser.token0 =
  let sp = coq_span start_pos end_pos in
  match raw with
  | Parser.MODULE -> Holdfast_checked_parser.MODULE sp
  | Parser.PUBLIC -> Holdfast_checked_parser.PUBLIC sp
  | Parser.NAT -> Holdfast_checked_parser.NAT sp
  | Parser.BOOL -> Holdfast_checked_parser.BOOL sp
  | Parser.LET -> Holdfast_checked_parser.LET sp
  | Parser.CONST -> Holdfast_checked_parser.CONST sp
  | Parser.RETURN -> Holdfast_checked_parser.RETURN sp
  | Parser.IF -> Holdfast_checked_parser.IF sp
  | Parser.ELSE -> Holdfast_checked_parser.ELSE sp
  | Parser.TRUE -> Holdfast_checked_parser.TRUE sp
  | Parser.FALSE -> Holdfast_checked_parser.FALSE sp
  | Parser.LPAREN -> Holdfast_checked_parser.LPAREN sp
  | Parser.RPAREN -> Holdfast_checked_parser.RPAREN sp
  | Parser.LBRACE -> Holdfast_checked_parser.LBRACE sp
  | Parser.RBRACE -> Holdfast_checked_parser.RBRACE sp
  | Parser.SEMICOLON -> Holdfast_checked_parser.SEMICOLON sp
  | Parser.COMMA -> Holdfast_checked_parser.COMMA sp
  | Parser.COLON -> Holdfast_checked_parser.COLON sp
  | Parser.DOT -> Holdfast_checked_parser.DOT sp
  | Parser.FATARROW -> Holdfast_checked_parser.FATARROW sp
  | Parser.EQUAL -> Holdfast_checked_parser.EQUAL sp
  | Parser.PLUS -> Holdfast_checked_parser.PLUS sp
  | Parser.MINUS -> Holdfast_checked_parser.MINUS sp
  | Parser.STAR -> Holdfast_checked_parser.STAR sp
  | Parser.SLASH -> Holdfast_checked_parser.SLASH sp
  | Parser.PERCENT -> Holdfast_checked_parser.PERCENT sp
  | Parser.EQ -> Holdfast_checked_parser.EQ0 sp
  | Parser.LE -> Holdfast_checked_parser.LE sp
  | Parser.NE -> Holdfast_checked_parser.NE sp
  | Parser.LT -> Holdfast_checked_parser.LT0 sp
  | Parser.GT -> Holdfast_checked_parser.GT0 sp
  | Parser.GE -> Holdfast_checked_parser.GE sp
  | Parser.AND -> Holdfast_checked_parser.AND sp
  | Parser.OR -> Holdfast_checked_parser.OR sp
  | Parser.NOT -> Holdfast_checked_parser.NOT sp
  | Parser.EOF -> Holdfast_checked_parser.EOF sp
  | Parser.IDENT s ->
      Holdfast_checked_parser.IDENT (Holdfast_checked_parser.Pair (sp, coq_string_of_string s))
  | Parser.DECIMAL s ->
      Holdfast_checked_parser.DECIMAL (Holdfast_checked_parser.Pair (sp, coq_string_of_string s))
  | _ ->
      raise (Ast.Refusal ("syntax", start_pos, "unexpected token or incomplete input"))

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

let validate_utf8 source =
  if String.starts_with ~prefix:"\\xEF\\xBB\\xBF" source then
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
      walk (index + width)
    end
  in
  walk 0

let position source target =
  let limit = min target (String.length source) in
  let rec scan index line column =
    if index >= limit then (line, column)
    else match source.[index] with
      | '\\r' ->
          let width = if index + 1 < limit && source.[index + 1] = '\\n' then 2 else 1 in
          scan (index + width) (line + 1) 1
      | '\\n' -> scan (index + 1) (line + 1) 1
      | character when Char.code character land 0xc0 = 0x80 ->
          scan (index + 1) line column
      | _ -> scan (index + 1) line (column + 1)
  in
  scan 0 1 1

let diagnostic source kind offset message =
  let line, column = position source offset in
  Ast.Object [("kind", Ast.String kind); ("line", Ast.Number line);
              ("column", Ast.Number column); ("message", Ast.String message)]

let rec token_stream state lexbuf current history =
  lazy (
    let raw = Lexer.token state lexbuf in
    let start_pos = Lexing.lexeme_start lexbuf in
    let end_pos = Lexing.lexeme_end lexbuf in
    current := start_pos;
    history := (start_pos, raw) :: !history;
    let tok = convert_token start_pos end_pos raw in
    Holdfast_checked_parser.MenhirLibParser.Inter.Buf_cons
      (tok, token_stream state lexbuf current history)
  )

let classify_failure state lexbuf default_offset history =
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

let parse_source_string raw_source =
  let current = ref 0 in
  let history = ref [] in
  try
    if String.length raw_source > Ast.max_source_bytes then
      raise (Ast.Refusal ("limit", 0, "source exceeds 65536 bytes"));
    validate_utf8 raw_source;
    let lexbuf = Lexing.from_string raw_source in
    let state = Lexer.create ~surface:false () in
    let stream = token_stream state lexbuf current history in
    let log_fuel = nat_of_int 30 in
    match Holdfast_checked_parser.file log_fuel stream with
    | Holdfast_checked_parser.MenhirLibParser.Inter.Parsed_pr (Holdfast_checked_parser.Accepted node, _) ->
        let syntax = ast_json_of_coq_json node.Holdfast_checked_parser.node_syntax in
        (0, Ast.encode (Ast.Object [("schema", Ast.Number 1); ("ast", syntax)]))
    | Holdfast_checked_parser.MenhirLibParser.Inter.Parsed_pr
        (Holdfast_checked_parser.Refused (kind, offset, message), _) ->
        (1, Ast.encode (diagnostic raw_source (string_of_coq_string kind)
                          (int_of_nat offset) (string_of_coq_string message)))
    | Holdfast_checked_parser.MenhirLibParser.Inter.Fail_pr_full _ ->
        let kind, offset, message = classify_failure state lexbuf !current !history in
        (1, Ast.encode (diagnostic raw_source kind offset message))
    | Holdfast_checked_parser.MenhirLibParser.Inter.Timeout_pr ->
        (1, Ast.encode (diagnostic raw_source "limit" !current "checked parser step fuel exhausted"))
  with
  | Ast.Refusal (kind, offset, message) ->
      (1, Ast.encode (diagnostic raw_source kind offset message))
  | Stack_overflow ->
      (1, Ast.encode (diagnostic raw_source "limit" !current "native parser stack limit exceeded"))
  | Sys_error message ->
      (1, Ast.encode (diagnostic raw_source "io" !current message))

let run_batch () =
  try
    while true do
      let header = input_line stdin in
      if header = "trace-worker-pid" then begin
        let stat = open_in "/proc/self/stat" in
        let pid = List.hd (String.split_on_char ' ' (input_line stat)) in
        close_in stat;
        Printf.printf "pid %d\\n%!" (int_of_string pid)
      end else begin
        let count =
          try int_of_string (String.trim header)
          with Failure _ -> -1
        in
        if count < 0 || count > Ast.max_source_bytes + 1 then begin
          let payload = Ast.encode (diagnostic "" "limit" 0 "source exceeds 65536 bytes") in
          output_string stdout ("1 " ^ payload ^ "\\n");
          flush stdout
        end else begin
          let raw_source = really_input_string stdin count in
          let code, payload = parse_source_string raw_source in
          output_string stdout (string_of_int code ^ " " ^ payload ^ "\\n");
          flush stdout
        end
      end
    done
  with End_of_file -> ()

let () =
  set_binary_mode_in stdin true;
  set_binary_mode_out stdout true;
  match Array.to_list Sys.argv with
  | [_] ->
      (try
         let raw_source = read_source () in
         let code, payload = parse_source_string raw_source in
         print_endline payload;
         if code <> 0 then exit code
       with
       | Ast.Refusal (kind, offset, message) ->
           print_endline (Ast.encode (diagnostic "" kind offset message));
           exit 1
       | Sys_error message ->
           print_endline (Ast.encode (diagnostic "" "io" 0 message));
           exit 1)
  | [_; "--batch"] -> run_batch ()
  | _ ->
      print_endline (Ast.encode (diagnostic "" "syntax" 0 "expected no arguments"));
      exit 1
"""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _strip_comments_and_actions(body: str) -> str:
    cleaned = re.sub(r"/\*.*?\*/", "", body, flags=re.DOTALL)
    out: list[str] = []
    depth = 0
    quote: str | None = None
    escape = False
    for ch in cleaned:
        if quote is not None:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == quote:
                quote = None
        elif ch in {'"', "'"} and depth > 0:
            quote = ch
        elif ch == "{":
            depth += 1
        elif ch == "}":
            if depth == 0:
                raise ValueError("unbalanced closing brace in parser.mly")
            depth -= 1
        elif depth == 0:
            out.append(ch)
    if depth != 0:
        raise ValueError("unbalanced opening brace in parser.mly")
    return "".join(out)


def _pure_grammar_view(mly_text: str) -> tuple[str, str]:
    """Verify the pure grammar skeleton in parser.mly and emit HoldFastPureGrammar.mly and a token stub."""
    header, sep, body = mly_text.partition("\n%%\n")
    if sep != "\n%%\n":
        raise ValueError("parser.mly is missing its %% section separator")
    declared_tokens: set[str] = set()
    constructors: list[str] = []
    for raw_line in header.splitlines():
        line = raw_line.strip()
        match = re.match(r"^%token(?:\s*<([^>]+)>)?\s+(.+)$", line)
        if match:
            payload = match.group(1)
            for token_name in match.group(2).split():
                declared_tokens.add(token_name)
                if payload:
                    constructors.append(f"  | {token_name} of ({payload})")
                else:
                    constructors.append(f"  | {token_name}")
    if not set(PURE_TERMINALS).issubset(declared_tokens):
        raise ValueError("parser.mly omits required pure terminals")
    cleaned = _strip_comments_and_actions(body)
    rule_header_re = re.compile(r"(?m)^\s*(?:%inline\s+)?([a-z_][a-z0-9_]*(?:\([^)]*\))?)\s*:")
    matches = list(rule_header_re.finditer(cleaned))
    rules: dict[str, tuple[tuple[str, ...], ...]] = {}
    for idx, match in enumerate(matches):
        head = re.sub(r"\s+", "", match.group(1))
        start = match.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(cleaned)
        rhs_block = cleaned[start:end].strip()
        alts: list[tuple[str, ...]] = []
        for raw_alt in rhs_block.split("|"):
            raw_e = re.sub(r"\b[a-z_][a-z0-9_]*\s*=\s*", "", raw_alt.strip())
            raw_e = re.sub(r"\(\s*", "(", raw_e)
            raw_e = re.sub(r"\s*\)", ")", raw_e)
            raw_e = re.sub(r"\s*,\s*", ",", raw_e)
            alts.append(tuple(raw_e.split()))
        rules[head] = tuple(alts)
    extracted = {name: rules.get(name, ()) for name in EXPECTED_PURE_SKELETON}
    if extracted != EXPECTED_PURE_SKELETON:
        raise ValueError("pure grammar skeleton in parser.mly drifted from the checked specification")
    token_stub = f"""(* SPDX-License-Identifier: Apache-2.0 *)
type token =
{"\n".join(constructors)}

exception Error
let generic_application_prefix _ _ : unit = raise Error
let format_expression _ _ : Ast.node * int * bool = raise Error
"""
    return HOLDFAST_PURE_GRAMMAR_MLY, token_stub


def _proof_openings(source: bytes, *, reference: bool = False) -> bytes:
    """Move only the three reviewed commands, or omit them in the diagnostic twin."""
    if _sha256(source) != INTERPRETER_SHA256:
        raise ValueError("unsupported Menhir Interpreter source; compatibility repair refused")
    lines = source.decode("utf-8").splitlines(keepends=True)
    for name in TARGETS:
        heads = [index for index, line in enumerate(lines)
                 if re.match(rf"^(?:Fixpoint|Definition) {name}\b", line)]
        if len(heads) != 1:
            raise ValueError(f"expected one reviewed declaration: {name}")
        start = heads[0]
        end = next(index for index in range(start + 1, len(lines))
                   if lines[index] == "Defined.\n")
        tactics = [index for index in range(start + 1, end)
                   if re.match(r"^(?:unshelve )?refine\b", lines[index])]
        proofs = [index for index in range(start + 1, end) if lines[index] == "Proof.\n"]
        if len(tactics) != 1 or len(proofs) != 1 or proofs[0] <= tactics[0]:
            raise ValueError(f"unsupported proof opening: {name}")
        command = lines.pop(proofs[0])
        if not reference:
            lines.insert(tactics[0], command)
    candidate = "".join(lines).encode("utf-8")
    wanted = REFERENCE_SHA256 if reference else CANDIDATE_SHA256
    if _sha256(candidate) != wanted:
        raise ValueError("Menhir proof-command repair differs from the reviewed candidate")
    return candidate


def _validator_items_map(source: bytes, *, reference: bool = False) -> bytes:
    """Keep IsItemsMap abstract in is_validator_forall_items so rocqchk does not unroll items_map."""
    if _sha256(source) != VALIDATOR_COMPLETE_SHA256:
        raise ValueError("unsupported Menhir Validator_complete source; items_map repair refused")
    if reference:
        return source
    old_block = (
        "Proof.\n"
        "  intros -> Hval1 Hval2 Val st prod fut lookahead (pos & -> & Hlookahead).\n"
        "  rewrite /forallb_items StateProdPosMap.fold_1 in Val.\n"
        "  assert (match future_of_prod prod pos with\n"
        "          | [] => b1 st prod pos (find_items_map (items_map ()) st prod pos)\n"
        "          | s :: fut' => b2 st prod pos (find_items_map (items_map ()) st prod pos) s fut'\n"
        "          end = true).\n"
        "  - unfold find_items_map in *.\n"
        "    assert (Hfind := @StateProdPosMap.find_2 _ (items_map ()) (st, prod, pos))."
    )
    new_block = (
        "Proof.\n"
        "  intros Him Hval1 Hval2 Val st prod fut lookahead (pos & -> & Hlookahead).\n"
        "  rewrite -Him in Hlookahead.\n"
        "  rewrite /forallb_items StateProdPosMap.fold_1 in Val.\n"
        "  assert (match future_of_prod prod pos with\n"
        "          | [] => b1 st prod pos (find_items_map im st prod pos)\n"
        "          | s :: fut' => b2 st prod pos (find_items_map im st prod pos) s fut'\n"
        "          end = true).\n"
        "  - unfold find_items_map in *.\n"
        "    assert (Hfind := @StateProdPosMap.find_2 _ im (st, prod, pos))."
    )
    text = source.decode("utf-8")
    if text.count(old_block) != 1:
        raise ValueError("unsupported Validator_complete proof opening")
    candidate = text.replace(old_block, new_block, 1).encode("utf-8")
    if _sha256(candidate) != VALIDATOR_COMPLETE_CANDIDATE_SHA256:
        raise ValueError("Menhir Validator_complete repair differs from the reviewed candidate")
    return candidate


def _check_closed_assumptions(reading: str, expected_count: int) -> None:
    """Refuse any concrete theorem whose Print Assumptions output is not closed."""
    lines = [line.strip() for line in reading.strip().splitlines() if line.strip()]
    if lines != ["Closed under the global context"] * expected_count:
        raise ValueError("concrete checked-parser theorem has unclosed assumptions")


def _release_sources(archive: bytes) -> dict[str, bytes]:
    """Read only the needed regular files from the authenticated immutable archive."""
    if len(archive) > MAX_ARCHIVE_BYTES or hashlib.sha512(archive).hexdigest() != ARCHIVE_SHA512:
        raise ValueError("Menhir release archive digest differs from the selected source")
    selected = {f"coq-menhirlib/src/{name}.v" for name in MODULES}
    selected.update(("coq-menhirlib/src/_CoqProject", *LICENSES))
    sources: dict[str, bytes] = {}
    total = 0
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as bundle:
        for ordinal, member in enumerate(bundle):
            if ordinal > 5000:
                raise ValueError("Menhir archive exceeds its member bound")
            parts = PurePosixPath(member.name).parts
            if len(parts) == 1 and member.isdir():
                continue
            if (len(parts) < 2 or PurePosixPath(member.name).is_absolute()
                    or ".." in parts or "\\" in member.name):
                raise ValueError("unsafe Menhir archive member")
            relative = PurePosixPath(*parts[1:]).as_posix()
            if relative not in selected:
                continue
            if relative in sources or not member.isfile() or member.size < 0:
                raise ValueError("ambiguous or non-regular Menhir source")
            total += member.size
            if total > MAX_ARCHIVE_BYTES:
                raise ValueError("Menhir support sources exceed their byte bound")
            stream = bundle.extractfile(member)
            if stream is None:
                raise ValueError("unreadable Menhir archive source")
            with stream:
                sources[relative] = read_bounded(stream, MAX_ARCHIVE_BYTES)
    if set(sources) != selected:
        raise ValueError("Menhir archive omits selected support sources")
    for name, wanted in (*LICENSES.items(), ("coq-menhirlib/src/Version.v", VERSION_SHA256)):
        if _sha256(sources[name]) != wanted:
            raise ValueError(f"Menhir reviewed source differs: {name}")
    return sources


def _opam(arguments: list[str], *, switch: str = proofenv.ROCQ_SWITCH) -> list[str]:
    return ["opam", "exec", "--switch", switch, "--", *arguments]


def _run(arguments: list[str], directory: Path, log: Path,
         steps: list[dict[str, object]], *, refusal: str | None = None,
         source: bytes | None = None) -> str:
    started = time.monotonic()
    try:
        done = subprocess.run(arguments, cwd=directory, capture_output=True,
                              input=source, timeout=TIMEOUT, check=False)
    except subprocess.TimeoutExpired as error:
        log.write_bytes((error.stdout or b"") + (error.stderr or b""))
        steps.append({"command": arguments, "directory": str(directory),
                      "status": "timeout", "log": str(log)})
        raise RuntimeError(f"Menhir support command exceeded {TIMEOUT} seconds: {arguments[0]}") from error
    # Keep the streams separate for byte-for-byte frozen-reading comparisons.
    log.write_bytes(done.stdout)
    error_log = log.with_suffix(".stderr")
    error_log.write_bytes(done.stderr)
    steps.append({"command": arguments, "directory": str(directory), "exit": done.returncode,
                  "seconds": round(time.monotonic() - started, 6), "stdout": str(log),
                  "stderr": str(error_log), "stdout_sha256": _sha256(done.stdout),
                  "stderr_sha256": _sha256(done.stderr)})
    output = done.stdout.decode("utf-8")
    detail = done.stderr.decode("utf-8")
    if refusal is not None:
        if done.returncode != 1 or refusal not in output + detail:
            raise RuntimeError("Menhir version mismatch did not produce the expected compiler refusal")
    elif done.returncode:
        raise RuntimeError(f"Menhir support command exited {done.returncode}: {(detail or output)[-3000:]}")
    return output


def _inputs(root: Path) -> dict[str, str]:
    return {name: file_sha256(root / name) for name in (
        "tools/opam/rocq.lock", "tools/opam/sail.lock", "tools/toolchain/parser_checked.py",
        "tools/toolchain/hashing.py", "tools/toolchain/atomic.py",
        "tools/toolchain/parser/ast.ml", "tools/toolchain/parser/parser.mly",
        "tools/toolchain/parser/lexer.mll", "examples/pure.hf",
        "examples/constants.hf", "examples/expressions.hf")}


def _toolchain(root: Path, directory: Path, steps: list[dict[str, object]]) -> dict[str, object]:
    sail = (root / "tools/opam/sail.lock").read_text(encoding="utf-8")
    if set(re.findall(r'"menhir\.([^"\s]+)"', sail)) != {RELEASE}:
        raise ValueError("support source does not match the Sail snapshot's Menhir generator")
    lock = (root / "tools/opam/rocq.lock").read_text(encoding="utf-8")
    if set(re.findall(r'"rocq-core\.([^"\s]+)"', lock)) != {proofenv.ROCQ_VERSION}:
        raise ValueError("support prover differs from the proof snapshot")
    version = _run(_opam(["rocq", "c", "--version"]), root,
                   directory / "toolchain.stdout", steps)
    found = re.search(r"\bversion\s+([^\s]+)", version)
    releases = {proofenv.ROCQ_VERSION, proofenv.ROCQ_VERSION.removesuffix(".0")}
    if found is None or found[1] not in releases:
        raise ValueError("Menhir support compiler differs from the locked prover")
    compiler = _run(_opam(["ocamlc", "-version"]), root,
                    directory / "ocaml.stdout", steps).strip()
    if compiler != proofenv.OCAML_VERSION:
        raise ValueError("Menhir support OCaml compiler differs from the project switch")
    binary = _run(["opam", "var", "bin", "--switch", proofenv.ROCQ_SWITCH], root,
                  directory / "tool-path.stdout", steps).strip()
    binary_dir = Path(binary)
    if not binary_dir.is_absolute():
        raise ValueError("opam returned a relative support tool directory")
    generator = _run(_opam(["menhir", "--version"], switch=env.SAIL_SWITCH), root,
                     directory / "menhir.stdout", steps).strip()
    if generator != f"menhir, version {RELEASE}":
        raise ValueError("Menhir generator executable differs from the locked release")
    sail_bin = _run(["opam", "var", "bin", "--switch", env.SAIL_SWITCH], root,
                    directory / "sail-tool-path.stdout", steps).strip()
    sail_bin_dir = Path(sail_bin)
    if not sail_bin_dir.is_absolute():
        raise ValueError("opam returned a relative generator tool directory")
    return {
        "switch": proofenv.ROCQ_SWITCH,
        "generator_switch": env.SAIL_SWITCH,
        "rocq": version.strip(),
        "ocamlc": compiler,
        "menhir": generator,
        "binary_sha256": {
            **{name: file_sha256(binary_dir / name)
               for name in ("rocq", "rocqchk", "ocamlc", "ocamlopt", "ocamllex")},
            "menhir": file_sha256(sail_bin_dir / "menhir"),
        },
    }


def _runtime(directory: Path, steps: list[dict[str, object]]) -> dict[str, object]:
    """Bind installed proof inputs, including every physical LoadPath root."""
    config = _run(_opam(["rocq", "c", "-config"]), directory,
                  directory / "runtime-config.stdout", steps)
    where = _run(_opam(["rocqchk", "-where"]), directory,
                 directory / "runtime-where.stdout", steps).strip()
    load_path = _run(_opam(["rocq", "top", "-q", "-quiet"]), directory,
                     directory / "runtime-loadpath.stdout", steps, source=b"Print LoadPath.\n")
    settings = dict(line.split("=", 1) for line in config.splitlines() if "=" in line)
    if any(key not in settings or not Path(settings[key]).is_absolute()
           for key in ("COQLIB", "COQCORELIB")):
        raise ValueError("unsupported Menhir support prover library configuration")
    roots = {Path(settings[key]).resolve() for key in ("COQLIB", "COQCORELIB")}
    if not where or not Path(where).is_absolute():
        raise ValueError("unsupported Menhir support kernel library path")
    roots.add(Path(where).resolve())
    # The prover prints long load-path rows on two lines on some platforms.
    listing = re.sub(r"\n\s+(/)", r" \1", load_path).splitlines()
    if not listing or listing[0] != "Installed / Logical Path / Physical path:":
        raise ValueError("unsupported Menhir support prover load-path listing")
    for line in listing[1:]:
        found = re.fullmatch(r"\s*(?:i\s+)?(?:<>|[\w.]+)\s+(/.+)", line)
        if found is None:
            raise ValueError("unsupported Menhir support prover load-path row")
        path = Path(found[1]).resolve()
        if path != directory.resolve():
            roots.add(path)
    minimal = sorted(path for path in roots
                     if not any(path != other and path.is_relative_to(other) for other in roots))
    inventory_paths: list[Path] = []
    for root in minimal:
        if not root.is_dir():
            raise ValueError("Menhir support installed library root is missing")
        for path in sorted(root.rglob("*")):
            if path.is_symlink() and path.is_dir():
                raise ValueError("Menhir support installed library has a directory alias")
            if path.is_file():
                inventory_paths.append(path)
    if not inventory_paths:
        raise ValueError("Menhir support installed library inventory is empty")
    with ThreadPoolExecutor(max_workers=min(16, os.process_cpu_count() or 1, len(inventory_paths))) as pool:
        digests = list(pool.map(file_sha256, inventory_paths))
    files = dict(zip((str(path) for path in inventory_paths), digests, strict=True))
    return {"config": config, "load_path": load_path, "files_sha256": files}


def _stage(sources: dict[str, bytes], directory: Path, *, reference: bool) -> None:
    directory.mkdir()
    for path, source in sources.items():
        relative = path.removeprefix("coq-menhirlib/src/")
        # The selected license notices accompany every private build tree.
        if path in LICENSES:
            relative = "LICENSE.generator" if path == "LICENSE" else "LICENSE.support"
        if relative == "Interpreter.v":
            content = _proof_openings(source, reference=reference)
        elif relative == "Validator_complete.v":
            content = _validator_items_map(source, reference=reference)
        else:
            content = source
        (directory / relative).write_bytes(content)


def _compile(directory: Path, steps: list[dict[str, object]], *, jobs: int | None = None) -> None:
    _run(_opam(["rocq", "makefile", "-f", "_CoqProject", "-o", "CoqMakefile"]),
         directory, directory / "makefile.stdout", steps)
    worker_jobs = jobs if jobs is not None else (os.process_cpu_count() or 2)
    _run(_opam(["make", "-f", "CoqMakefile", f"-j{worker_jobs}"]),
         directory, directory / "compile.stdout", steps)


def _compile_grammar_and_extract(tree: Path, pure_mly: str, steps: list[dict[str, object]]) -> None:
    (tree / "HoldFastPureAst.v").write_text(HOLDFAST_PURE_AST_V, encoding="utf-8", newline="")
    (tree / "HoldFastPureGrammar.mly").write_text(pure_mly, encoding="utf-8", newline="")
    _run(_opam(["menhir", "--coq", "--strict", "HoldFastPureGrammar.mly"], switch=env.SAIL_SWITCH),
         tree, tree / "menhir-coq.stdout", steps)
    for module_name in GRAMMAR_MODULES:
        if module_name == "HoldFastPureProofs":
            (tree / "HoldFastPureProofs.v").write_text(HOLDFAST_PURE_PROOFS_V, encoding="utf-8", newline="")
        _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", f"{module_name}.v"]),
             tree, tree / f"{module_name.lower()}.stdout", steps)
    (tree / "HoldFastPureExtraction.v").write_text(HOLDFAST_PURE_EXTRACTION_V, encoding="utf-8", newline="")
    _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", "HoldFastPureExtraction.v"]),
         tree, tree / "extraction.stdout", steps)


def _work_root(root: Path) -> Path:
    directory = proofenv.lane_root(proofenv.lane_of(root)) / "holdfast-parser-checked"
    kind = proofenv.filesystem(directory)
    if not kind or kind in proofenv.CROSS_OS_FILESYSTEMS | proofenv.VOLATILE_FILESYSTEMS:
        raise ValueError("Menhir support outputs require a persistent native filesystem")
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _runtime_root() -> Path:
    directory = proofenv.build_root() / "holdfast-parser-checked-runtime"
    kind = proofenv.filesystem(directory)
    if not kind or kind in proofenv.CROSS_OS_FILESYSTEMS | proofenv.VOLATILE_FILESYSTEMS:
        raise ValueError("checked parser runtime requires a persistent native filesystem")
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _read_file_bytes(path: Path) -> bytes:
    with path.open("rb") as stream:
        return stream.read()


RUNTIME_INPUT_PATHS = (
    "tools/toolchain/parser/ast.ml",
    "tools/toolchain/parser/lexer.mll",
    "tools/toolchain/parser/parser.mly",
    "tools/opam/sail.lock",
    "tools/opam/rocq.lock",
)


def _runtime_inputs(root: Path) -> dict[str, str]:
    files = {path: file_sha256(root / path) for path in RUNTIME_INPUT_PATHS}
    return {
        **files,
        "archive_sha512": ARCHIVE_SHA512,
        "candidate_sha256": CANDIDATE_SHA256,
        "validator_complete_candidate_sha256": VALIDATOR_COMPLETE_CANDIDATE_SHA256,
        "holdfast_pure_ast_v_sha256": _sha256(HOLDFAST_PURE_AST_V.encode("utf-8")),
        "holdfast_pure_proofs_v_sha256": _sha256(HOLDFAST_PURE_PROOFS_V.encode("utf-8")),
        "holdfast_pure_extraction_v_sha256": _sha256(HOLDFAST_PURE_EXTRACTION_V.encode("utf-8")),
        "checked_main_ml_sha256": _sha256(CHECKED_MAIN_ML.encode("utf-8")),
        "ocaml_backend": "ocamlopt",
    }


def _compile_checked_executable(root: Path, tree: Path, token_stub: str,
                                steps: list[dict[str, object]]) -> Path:
    for name in ("ast.ml", "lexer.mll"):
        shutil.copyfile(root / "tools/toolchain/parser" / name, tree / name)
    (tree / "parser.ml").write_text(token_stub, encoding="utf-8", newline="")
    (tree / "checked_main.ml").write_text(CHECKED_MAIN_ML, encoding="utf-8", newline="")
    ocaml_commands = (
        ("ast-compile", ["ocamlopt", "-c", "ast.ml"]),
        ("token-stub-compile", ["ocamlopt", "-c", "parser.ml"]),
        ("lexer-generate", ["ocamllex", "lexer.mll"]),
        ("lexer-compile", ["ocamlopt", "-c", "lexer.ml"]),
        ("extracted-mli-compile", ["ocamlopt", "-w", "-a", "-c", "holdfast_checked_parser.mli"]),
        ("extracted-ml-compile", ["ocamlopt", "-w", "-a", "-c", "holdfast_checked_parser.ml"]),
        ("checked-main-compile", ["ocamlopt", "-c", "checked_main.ml"]),
        ("checked-link", ["ocamlopt", "-o", "holdfast-checked-parser", "ast.cmx",
                          "parser.cmx", "lexer.cmx", "holdfast_checked_parser.cmx", "checked_main.cmx"]),
    )
    for step_name, cmd in ocaml_commands:
        _run(_opam(cmd), tree, tree / f"{step_name}.stdout", steps)
    return tree / "holdfast-checked-parser"


def _publish_runtime_build(runtime_dir: Path, source_tree: Path, wanted: dict[str, str]) -> holdfast_parser.Build:
    exe_path = runtime_dir / "holdfast-checked-parser"
    receipt_path = runtime_dir / "receipt.json"
    exe_bytes = _read_file_bytes(source_tree / "holdfast-checked-parser")
    with atomic_path(exe_path) as pending_exe:
        pending_exe.write_bytes(exe_bytes)
        pending_exe.chmod(0o755)
    receipt: dict[str, object] = {
        "schema": 1,
        "scope": "holdfast-checked-pure-parser-runtime",
        "status": "built",
        "directory": str(runtime_dir),
        "inputs": wanted,
        "generated_sha256": {
            "holdfast-parser": _sha256(exe_bytes),
            "holdfast_checked_parser.ml": file_sha256(source_tree / "holdfast_checked_parser.ml"),
            "holdfast_checked_parser.mli": file_sha256(source_tree / "holdfast_checked_parser.mli"),
            "HoldFastPureGrammar.v": file_sha256(source_tree / "HoldFastPureGrammar.v"),
        },
    }
    publish_report(receipt_path, receipt)
    return holdfast_parser.Build(runtime_dir, exe_path, receipt)


def _runtime_entry(cache: Path, wanted: dict[str, str]) -> Path:
    digest = _sha256(json.dumps(wanted, sort_keys=True).encode("utf-8"))
    directory = cache / "builds" / digest
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _read_runtime(directory: Path, wanted: dict[str, str], *, legacy: bool = False) -> holdfast_parser.Build | None:
    receipt_path = directory / "receipt.json"
    if not receipt_path.is_file():
        return None
    try:
        receipt = cast("dict[str, object]", json.loads(_read_file_bytes(receipt_path).decode("utf-8")))
    except (UnicodeDecodeError, ValueError) as error:
        raise ValueError("checked parser runtime receipt is malformed") from error
    _require(isinstance(receipt, dict), "checked parser runtime receipt is malformed")
    if receipt.get("inputs") != wanted:
        _require(legacy, "checked parser cache receipt names different inputs")
        return None
    outputs = receipt.get("generated_sha256")
    exe = directory / "holdfast-checked-parser"
    if not isinstance(outputs, dict) or not exe.is_file() or file_sha256(exe) != outputs.get("holdfast-parser"):
        raise ValueError("checked parser executable changed after its build")
    return holdfast_parser.Build(directory, exe, receipt)


def _install_runtime_build(root: Path, source_tree: Path, contents: bytes | None = None) -> holdfast_parser.Build:
    cache = _runtime_root()
    wanted = _runtime_inputs(root)
    directory = _runtime_entry(cache, wanted)
    with holdfast_parser._file_lock(directory / "runtime.lock", timeout=TIMEOUT):
        if contents is not None:
            with holdfast_parser._file_lock(cache / "runtime.lock", timeout=TIMEOUT), atomic_path(cache / "menhir.tar.gz") as pending_tar:
                pending_tar.write_bytes(contents)
        return _publish_runtime_build(directory, source_tree, wanted)


def ensure_checked_build(root: Path | None = None, *, archive: Path | None = None) -> holdfast_parser.Build:
    """Return the receipt-verified parser published for this checkout's exact runtime inputs."""
    repo = Path(__file__).resolve().parents[2] if root is None else root
    cache = _runtime_root()
    wanted = _runtime_inputs(repo)
    directory = _runtime_entry(cache, wanted)
    with holdfast_parser._file_lock(directory / "runtime.lock", timeout=TIMEOUT):
        cached = _read_runtime(directory, wanted)
        if cached is not None:
            return cached
        with holdfast_parser._file_lock(cache / "runtime.lock", timeout=TIMEOUT):
            # Reuse a verified shared-cache entry under the lock that protects its receipt.
            legacy = _read_runtime(cache, wanted, legacy=True)
            if legacy is not None:
                exe = directory / "holdfast-checked-parser"
                copied = _read_file_bytes(legacy.executable)
                outputs = cast("dict[str, str]", legacy.receipt["generated_sha256"])
                _require(_sha256(copied) == outputs["holdfast-parser"], "checked parser executable changed after its build")
                with atomic_path(exe) as pending:
                    pending.write_bytes(copied)
                    pending.chmod(0o755)
                receipt = {**legacy.receipt, "directory": str(directory)}
                publish_report(directory / "receipt.json", receipt)
                return holdfast_parser.Build(directory, exe, receipt)
            return _build_runtime(repo, cache, directory, wanted, archive)


def _build_runtime(repo: Path, cache: Path, directory: Path,
                   wanted: dict[str, str], archive: Path | None) -> holdfast_parser.Build:
    stage_dir = cache / "stage"
    menhirlib_stamp: dict[str, object] = {
        "archive_sha512": ARCHIVE_SHA512,
        "candidate_sha256": CANDIDATE_SHA256,
        "validator_complete_candidate_sha256": VALIDATOR_COMPLETE_CANDIDATE_SHA256,
        "rocq_lock": wanted["tools/opam/rocq.lock"],
    }
    stamp_path = stage_dir / "menhirlib.json"
    reuse_menhirlib = False
    if stamp_path.is_file() and all((stage_dir / f"{name}.vo").is_file() for name in MODULES):
        try:
            reuse_menhirlib = json.loads(_read_file_bytes(stamp_path).decode("utf-8")) == menhirlib_stamp
        except (OSError, UnicodeDecodeError, ValueError):
            reuse_menhirlib = False
    steps: list[dict[str, object]] = []
    if not reuse_menhirlib:
        shutil.rmtree(stage_dir, ignore_errors=True)
        cached_tar = cache / "menhir.tar.gz"
        contents = _archive(cached_tar, cache) if archive is None and cached_tar.is_file() else None
        if contents is None or hashlib.sha512(contents).hexdigest() != ARCHIVE_SHA512:
            contents = _archive(archive, cache)
        sources = _release_sources(contents)
        _stage(sources, stage_dir, reference=False)
        _compile(stage_dir, steps)
        publish_report(stamp_path, menhirlib_stamp)
    mly_source = _read_file_bytes(repo / "tools/toolchain/parser/parser.mly").decode("utf-8")
    pure_mly, token_stub = _pure_grammar_view(mly_source)
    _compile_grammar_and_extract(stage_dir, pure_mly, steps)
    _compile_checked_executable(repo, stage_dir, token_stub, steps)
    _require(_runtime_inputs(repo) == wanted, "checked parser runtime inputs changed during build")
    return _publish_runtime_build(directory, stage_dir, wanted)


def print_guest_executable(root: Path) -> None:
    """Ensure the WSL guest checked-parser executable is built and print its path and digest."""
    compiled = ensure_checked_build(root)
    outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
    print(f"{compiled.executable} {outputs['holdfast-parser']}", flush=True)


_POPEN = subprocess.Popen
_WORKER_LOCK = threading.Lock()
_WORKER_STATE: dict[str, object] = {"proc": None, "key": None, "command": None}


def reset_checked_worker() -> None:
    """Terminate any persistent checked-parser batch worker."""
    with _WORKER_LOCK:
        proc = cast("subprocess.Popen[bytes] | None", _WORKER_STATE.get("proc"))
        _WORKER_STATE["proc"] = None
        _WORKER_STATE["key"] = None
        _WORKER_STATE["command"] = None
        _close_proc(proc)


atexit.register(reset_checked_worker)


def _run_wsl_probe(command: list[str], cwd: Path) -> tuple[int, bytes, bytes]:
    """Run a bounded WSL probe subprocess and return `(returncode, stdout, stderr)`."""
    probe = _POPEN(
        command,
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        out_bytes, err_bytes = probe.communicate(timeout=TIMEOUT)
    except subprocess.TimeoutExpired as error:
        probe.kill()
        probe.communicate()
        raise RuntimeError("WSL checked parser build exceeded timeout") from error
    return int(probe.returncode), out_bytes, err_bytes


def _probe_wsl_checked_cache(inputs_digest: str, wanted: dict[str, str], cwd: Path) -> tuple[int, bytes, bytes]:
    """Check the guest ext4 runtime cache without touching /mnt/c or importing toolchain."""
    fast_script = """import hashlib, json, os, pathlib, sys
digest, wanted = sys.argv[1], json.loads(sys.argv[2])
root = pathlib.Path(os.environ.get('VOS_BUILD_ROOT') or '/root/build') / 'holdfast-parser-checked-runtime' / 'builds' / digest
receipt_path = root / 'receipt.json'
if not receipt_path.is_file():
    raise SystemExit(3)
try:
    receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
except (OSError, UnicodeDecodeError, ValueError):
    sys.stderr.write('checked parser runtime receipt is malformed\\n')
    raise SystemExit(2)
if not isinstance(receipt, dict) or receipt.get('inputs') != wanted:
    sys.stderr.write('checked parser cache receipt names different inputs\\n')
    raise SystemExit(2)
exe = root / 'holdfast-checked-parser'
outputs = receipt.get('generated_sha256')
if not isinstance(outputs, dict) or not exe.is_file() or hashlib.sha256(exe.read_bytes()).hexdigest() != outputs.get('holdfast-parser'):
    sys.stderr.write('checked parser executable changed after its build\\n')
    raise SystemExit(2)
print(f"{exe} {outputs['holdfast-parser']}")"""
    return _run_wsl_probe(
        ["wsl", "-u", "root", "--cd", "/root", "-e", "/root/build/venv-linux/bin/python",
         "-c", fast_script, inputs_digest, json.dumps(wanted, sort_keys=True)],
        cwd,
    )


def _ensure_worker_command(repo: Path) -> list[str]:
    if sys.platform == "linux":
        runtime_dir = _runtime_root()
        wanted = _runtime_inputs(repo)
        inputs_digest = _sha256(json.dumps(wanted, sort_keys=True).encode("utf-8"))
        cached_cmd = _WORKER_STATE.get("command")
        if (_WORKER_STATE.get("key") == ("linux", str(runtime_dir), inputs_digest)
                and isinstance(cached_cmd, list)):
            return cast("list[str]", cached_cmd)
        compiled = ensure_checked_build(repo)
        outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
        key = ("linux", str(runtime_dir), inputs_digest)
        command = [str(compiled.executable), "--batch"]
        _WORKER_STATE["key"] = key
        _WORKER_STATE["command"] = command
        proc = cast("subprocess.Popen[bytes] | None", _WORKER_STATE.get("proc"))
        _WORKER_STATE["proc"] = None
        _close_proc(proc)
        _ = outputs["holdfast-parser"]
        return command
    if sys.platform == "win32":
        wanted = _runtime_inputs(repo)
        inputs_digest = _sha256(json.dumps(wanted, sort_keys=True).encode("utf-8"))
        cached_cmd = _WORKER_STATE.get("command")
        if _WORKER_STATE.get("key") == ("win32", inputs_digest) and isinstance(cached_cmd, list):
            return cast("list[str]", cached_cmd)
        returncode, out_bytes, err_bytes = _probe_wsl_checked_cache(inputs_digest, wanted, repo)
        if returncode == 2:
            detail = (err_bytes or out_bytes).decode("utf-8", errors="replace").strip()
            if "changed after its build" in detail:
                raise ValueError("checked parser executable changed after its build")
            raise RuntimeError(f"WSL checked parser setup exited {returncode}: {detail}")
        if returncode != 0:
            script = (
                "import sys; sys.path.insert(0, 'tools'); "
                "from pathlib import Path; "
                "from toolchain import parser_checked; "
                "parser_checked.print_guest_executable(Path.cwd())"
            )
            returncode, out_bytes, err_bytes = _run_wsl_probe(
                ["wsl", "-u", "root", "-e", "/usr/bin/env", "OPAMROOT=/root/.opam",
                 "/root/build/venv-linux/bin/python", "-c", script],
                repo,
            )
        if returncode != 0:
            detail = (err_bytes or out_bytes).decode("utf-8", errors="replace").strip()
            if "changed after its build" in detail:
                raise ValueError("checked parser executable changed after its build")
            raise RuntimeError(f"WSL checked parser setup exited {returncode}: {detail}")
        fields = out_bytes.decode("utf-8", errors="replace").strip().splitlines()[-1].split()
        if len(fields) != 2 or not fields[0].startswith("/"):
            raise ValueError("WSL checked parser setup returned an invalid executable descriptor")
        command = ["wsl", "-u", "root", "--cd", "/root", "-e", fields[0], "--batch"]
        proc = cast("subprocess.Popen[bytes] | None", _WORKER_STATE.get("proc"))
        _WORKER_STATE["proc"] = None
        _close_proc(proc)
        _WORKER_STATE["key"] = ("win32", inputs_digest)
        _WORKER_STATE["command"] = command
        return command
    raise RuntimeError(f"unsupported host platform for checked parser: {sys.platform}")


def parse_checked(source: bytes, *, root: Path | None = None,
                  compiled: holdfast_parser.Build | None = None) -> dict[str, holdfast_parser.Json]:
    """Parse pure HoldFast source through the Rocq-extracted holdfast-checked-parser."""
    source_text(source)
    if compiled is not None:
        outputs = cast("dict[str, str]", compiled.receipt["generated_sha256"])
        if (not compiled.executable.is_file()
                or file_sha256(compiled.executable) != outputs.get("holdfast-parser")):
            raise ValueError("checked parser executable changed after its build")
        return holdfast_parser.parse_source(compiled, source, surface=False)
    repo = Path(__file__).resolve().parents[2] if root is None else root
    frame = f"{len(source)}\n".encode("ascii") + source
    with _WORKER_LOCK:
        command = _ensure_worker_command(repo)
        line = b""
        for _attempt in range(2):
            proc = cast("subprocess.Popen[bytes] | None", _WORKER_STATE.get("proc"))
            if proc is None or proc.poll() is not None:
                proc = _POPEN(
                    command,
                    cwd=repo,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                _WORKER_STATE["proc"] = proc
            assert proc.stdin is not None and proc.stdout is not None  # noqa: S101
            try:
                proc.stdin.write(frame)
                proc.stdin.flush()
                line = proc.stdout.readline()
            except OSError:
                line = b""
            if line:
                break
            _WORKER_STATE["proc"] = None
            _close_proc(proc)
        if not line:
            raise RuntimeError("checked parser batch worker terminated without a response")
    code, raw_json = parse_batch_reply_line(
        line, error_message="checked parser returned a malformed batch response",
    )
    return holdfast_parser.decode_response(source, code, raw_json, surface=False)


def trace_worker_pids() -> tuple[int, int]:
    """Identify the live transport and parser processes that serve the measured requests."""
    parse_checked(b"module TraceRuntime; public Nat Id(Nat n) => n;")
    with _WORKER_LOCK:
        proc = cast("subprocess.Popen[bytes]", _WORKER_STATE["proc"])
        if not proc or not proc.stdin or not proc.stdout or proc.poll() is not None:
            raise ValueError("checked parser worker is unavailable")
        proc.stdin.write(b"trace-worker-pid\n")
        proc.stdin.flush()
        reply = re.fullmatch(rb"pid ([1-9][0-9]{0,9})\n", proc.stdout.readline(32))
        if reply is None:
            raise ValueError("checked parser returned an invalid worker identity")
        return proc.pid, int(reply[1])


def _archive(path: Path | None, directory: Path) -> bytes:
    if path is not None:
        with path.open("rb") as stream:
            return read_bounded(stream, MAX_ARCHIVE_BYTES)
    with urllib.request.urlopen(ARCHIVE_URL, timeout=TIMEOUT) as response:
        source = read_bounded(response, MAX_ARCHIVE_BYTES)
    (directory / "menhir.tar.gz").write_bytes(source)
    return source


def _observations(candidate: Path, reference: Path, guard: str,
                  steps: list[dict[str, object]]) -> dict[str, str]:
    probes = {candidate / "Frozen.v": FROZEN_QUERY, reference / "Frozen.v": FROZEN_QUERY,
              candidate / "Assumptions.v": ASSUMPTIONS_QUERY,
              candidate / "VersionAccepted.v": guard,
              candidate / "VersionRefused.v": guard.replace(f"require_{RELEASE}", "require_unreleased")}
    for path, text in probes.items():
        _require(path.read_bytes() == text.encode(), "Menhir support probe changed during qualification")
    for step in steps:
        for stream in ("stdout", "stderr"):
            _require(file_sha256(Path(str(step[stream]))) == step[f"{stream}_sha256"],
                     "Menhir support transcript changed during qualification")
    return {str(path): _sha256(text.encode()) for path, text in probes.items()}


def qualify(root: Path, *, archive: Path | None = None) -> dict[str, object]:
    """Freshly build, compare, kernel-check, extract and qualify the checked pure parser."""
    from filelock import FileLock  # noqa: PLC0415

    work = _work_root(root)
    with FileLock(work / "qualification.lock", timeout=1):
        latest = work / "qualification.json"
        latest.unlink(missing_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="support-", dir=work))
        steps: list[dict[str, object]] = []
        attempt: dict[str, object] = {"schema": 1, "scope": "holdfast-checked-pure-parser",
                                      "directory": str(directory), "steps": steps, "status": "running"}
        try:
            inputs = _inputs(root)
            tools = _toolchain(root, directory, steps)
            runtime = _runtime(directory, steps)
            contents = _archive(archive, directory)
            sources = _release_sources(contents)
            mly_source = (root / "tools/toolchain/parser/parser.mly").read_text(encoding="utf-8")
            pure_mly, token_stub = _pure_grammar_view(mly_source)
            candidate, reference = directory / "candidate", directory / "reference"
            _stage(sources, candidate, reference=False)
            _stage(sources, reference, reference=True)
            tree_jobs = max(1, (os.process_cpu_count() or 2) // 2)

            def _build_tree(tree: Path) -> list[dict[str, object]]:
                tree_steps: list[dict[str, object]] = []
                _compile(tree, tree_steps, jobs=tree_jobs)
                (tree / "Frozen.v").write_text(FROZEN_QUERY, encoding="utf-8", newline="")
                _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", "Frozen.v"]),
                     tree, tree / "frozen.stdout", tree_steps)
                _compile_grammar_and_extract(tree, pure_mly, tree_steps)
                return tree_steps

            with ThreadPoolExecutor(max_workers=2) as pool:
                cand_steps, ref_steps = list(pool.map(_build_tree, (candidate, reference)))
            steps.extend(cand_steps)
            steps.extend(ref_steps)
            generated_v = (candidate / "HoldFastPureGrammar.v").read_bytes()
            _require(bool(generated_v) and generated_v == (reference / "HoldFastPureGrammar.v").read_bytes(),
                     "fresh menhir --coq --strict generation changed HoldFastPureGrammar.v bytes")
            _require(f"MenhirLib.Version.require_{RELEASE}".encode() in generated_v,
                     "generated HoldFastPureGrammar.v omits the MenhirLib version guard")
            extracted_ml = (candidate / "holdfast_checked_parser.ml").read_bytes()
            extracted_mli = (candidate / "holdfast_checked_parser.mli").read_bytes()
            _require(bool(extracted_ml) and extracted_ml == (reference / "holdfast_checked_parser.ml").read_bytes()
                     and bool(extracted_mli) and extracted_mli == (reference / "holdfast_checked_parser.mli").read_bytes(),
                     "fresh Rocq extraction changed holdfast_checked_parser.ml/.mli bytes")
            outputs = {str(tree.name): {f"{name}.vo": file_sha256(tree / f"{name}.vo")
                                       for name in ALL_MODULES} for tree in (candidate, reference)}
            frozen = (candidate / "frozen.stdout").read_bytes()
            _require(bool(frozen) and frozen == (reference / "frozen.stdout").read_bytes(),
                     "same-prover Menhir public types, bodies, universes or assumptions differ")
            proofs_reading = (candidate / "holdfastpureproofs.stdout").read_text(encoding="utf-8")
            _require(proofs_reading.encode() == (reference / "holdfastpureproofs.stdout").read_bytes(),
                     "concrete checked-parser assumption reading differs between candidate and reference")
            _check_closed_assumptions(proofs_reading, len(THEOREMS))
            _run(_opam(["rocqchk", "-R", ".", "MenhirLib",
                        *(f"MenhirLib.{module}" for module in ALL_MODULES)]),
                 candidate, candidate / "kernel.stdout", steps)
            (candidate / "Assumptions.v").write_text(ASSUMPTIONS_QUERY, encoding="utf-8", newline="")
            _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", "Assumptions.v"]),
                 candidate, candidate / "assumptions.stdout", steps)
            guard = f"From MenhirLib Require Version.\nDefinition generator_version : unit := Version.require_{RELEASE}.\n"
            (candidate / "VersionAccepted.v").write_text(guard, encoding="utf-8", newline="")
            _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", "VersionAccepted.v"]),
                 candidate, candidate / "guard-accepted.stdout", steps)
            (candidate / "VersionRefused.v").write_text(
                guard.replace(f"require_{RELEASE}", "require_unreleased"), encoding="utf-8", newline="")
            _run(_opam(["rocq", "c", "-R", ".", "MenhirLib", "VersionRefused.v"]),
                 candidate, candidate / "guard-refused.stdout", steps, refusal="require_unreleased")
            checked_exe = _compile_checked_executable(root, candidate, token_stub, steps)
            checked_build = holdfast_parser.Build(
                directory=candidate,
                executable=checked_exe,
                receipt={"generated_sha256": {"holdfast-parser": file_sha256(checked_exe)}},
            )
            passed_fixtures = holdfast_parser._fixtures(checked_build)
            if (root / "tools/toolchain/parser/parser.mly").is_file():
                _install_runtime_build(root, candidate, contents)
                reset_checked_worker()
            dev_build = holdfast_parser.build(root)
            examples_verified: dict[str, str] = {}
            for rel_example in ("examples/pure.hf", "examples/constants.hf", "examples/expressions.hf"):
                example_bytes = holdfast_parser.read_source(root / rel_example)
                checked_parsed = holdfast_parser.parse_source(checked_build, example_bytes)
                dev_parsed = holdfast_parser.parse_source(dev_build, example_bytes)
                _require(checked_parsed == dev_parsed,
                         f"holdfast-checked-parser disagreed with holdfast-parser on {rel_example}")
                examples_verified[rel_example] = _sha256(example_bytes)
            migration_cases = migration.authored_cases(root)
            migration_report = migration.compare(checked_build, migration_cases)
            _require(migration_report.get("status") == "agreed" and not migration_report.get("differences"),
                     "holdfast-checked-parser disagreed with pure migration fixtures")
            _require(_inputs(root) == inputs and _toolchain(root, directory, steps) == tools,
                     "support qualification inputs or toolchain changed during execution")
            _require(_runtime(directory, steps) == runtime,
                     "support installed library inputs changed during execution")
            for tree, interp_wanted, vc_wanted in (
                (candidate, CANDIDATE_SHA256, VALIDATOR_COMPLETE_CANDIDATE_SHA256),
                (reference, REFERENCE_SHA256, VALIDATOR_COMPLETE_SHA256),
            ):
                for path, source in sources.items():
                    name = path.removeprefix("coq-menhirlib/src/")
                    if path in LICENSES:
                        name = "LICENSE.generator" if path == "LICENSE" else "LICENSE.support"
                    if name == "Interpreter.v":
                        digest = interp_wanted
                    elif name == "Validator_complete.v":
                        digest = vc_wanted
                    else:
                        digest = _sha256(source)
                    _require(file_sha256(tree / name) == digest,
                             "Menhir support source changed during qualification")
                for name, digest in outputs[tree.name].items():
                    _require(file_sha256(tree / name) == digest,
                             "Menhir support compiled output changed during qualification")
            probes = _observations(candidate, reference, guard, steps)
            report: dict[str, object] = {
                **attempt, "status": "passed", "inputs": inputs, "toolchain": tools,
                "installed_libraries": runtime, "compiled_sha256": outputs, "probes_sha256": probes,
                "generator_pair_qualified": True, "checked_holdfast_parser": True, "python_retired": True,
                "host_routes": ["linux", "win32"],
                "source": {"release": RELEASE, "url": ARCHIVE_URL,
                           "sha512": ARCHIVE_SHA512, "sha256": _sha256(contents),
                           "licenses": LICENSES, "files_sha256": {
                               path: _sha256(source) for path, source in sources.items()}},
                "repair": {"upstream_commit": UPSTREAM_REPAIR,
                           "scope": "relocate-three-existing-Proof-commands-and-abstract-IsItemsMap-in-is_validator_forall_items",
                           "candidate_sha256": CANDIDATE_SHA256,
                           "diagnostic_reference_sha256": REFERENCE_SHA256,
                           "validator_complete_candidate_sha256": VALIDATOR_COMPLETE_CANDIDATE_SHA256,
                           "validator_complete_reference_sha256": VALIDATOR_COMPLETE_SHA256,
                           "public_reading_equal": True, "reading_sha256": _sha256(frozen),
                           "query_sha256": _sha256(FROZEN_QUERY.encode())},
                "grammar": {
                    "owner": "tools/toolchain/parser/parser.mly",
                    "terminals": list(PURE_TERMINALS),
                    "rules": list(EXPECTED_PURE_SKELETON),
                    "holdfast_pure_ast_v_sha256": _sha256(HOLDFAST_PURE_AST_V.encode()),
                    "holdfast_pure_grammar_mly_sha256": _sha256(pure_mly.encode()),
                    "holdfast_pure_grammar_v_sha256": _sha256(generated_v),
                    "holdfast_pure_proofs_v_sha256": _sha256(HOLDFAST_PURE_PROOFS_V.encode()),
                    "deterministic_generation": True,
                },
                "extraction": {
                    "holdfast_pure_extraction_v_sha256": _sha256(HOLDFAST_PURE_EXTRACTION_V.encode()),
                    "holdfast_checked_parser_ml_sha256": _sha256(extracted_ml),
                    "holdfast_checked_parser_mli_sha256": _sha256(extracted_mli),
                    "holdfast_checked_parser_exe_sha256": file_sha256(checked_exe),
                    "deterministic_extraction": True,
                    "pure_fixtures_passed": len(passed_fixtures),
                    "examples_verified_sha256": examples_verified,
                    "migration_fixtures_agreed": len(migration_cases),
                },
                "kernel": {"status": "passed", "recursive": True,
                           "roots": [f"MenhirLib.{module}" for module in ALL_MODULES]},
                "version_guard": {"preserved_source_sha256": VERSION_SHA256,
                                  "accepted": f"require_{RELEASE}", "refused": "require_unreleased"},
                "assumptions": {"scope": "concrete-pure-grammar-and-abstract-support-boundary",
                                "closed_assumptions_accepted": True,
                                "theorems": list(THEOREMS),
                                "concrete_reading": proofs_reading,
                                "concrete_reading_sha256": _sha256(proofs_reading.encode()),
                                "roots": [f"SupportBoundary.Parser.{name}" for name in (
                                    "parse_correct", "parse_complete", "unambiguity")],
                                "query_sha256": _sha256(ASSUMPTIONS_QUERY.encode()),
                                "reading": (candidate / "assumptions.stdout").read_text(encoding="utf-8"),
                                "reading_sha256": file_sha256(candidate / "assumptions.stdout")},
                "deferred": [],
            }
            publish_report(directory / "qualification.json", report)
            publish_report(latest, report)
        except (OSError, RuntimeError, TypeError, ValueError) as error:
            attempt.update(status="failed", reason=str(error))
            publish_report(directory / "attempt.json", attempt)
            raise
        else:
            return report
