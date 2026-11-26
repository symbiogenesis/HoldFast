# SPDX-License-Identifier: Apache-2.0
"""Command descriptions and dispatch requirements for the repository tools."""

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Command:
    """Identify a command's handler, help text, and execution lane."""

    name: str
    module: str
    decides: str
    lane: str = "host"
    host_ok: frozenset[str] = field(default_factory=frozenset)

    def guest_only(self, argv: list[str]) -> bool:
        """Return whether this invocation needs WSL when launched on Windows."""
        if self.lane != "guest":
            return False
        return not argv or argv[0] not in self.host_ok


COMMANDS: tuple[Command, ...] = (
    Command("validate", "toolchain.cli.validate",
            "run logged local checks and tests; --static and --full select explicit coverage"),
    Command("gate", "toolchain.cli.gate",
            "run check, markdown, and typecheck in one static verdict"),
    Command("check", "toolchain.cli.check",
            "repository hygiene, licensing, source-comment links, and plan-summary arithmetic"),
    Command("markdown", "toolchain.cli.markdown",
            "closed-world Markdown linting and link validation under pinned rumdl"),
    Command("typecheck", "toolchain.cli.typecheck",
            "the tools' own Python, under two pinned checkers"),
    Command("prepare", "toolchain.cli.prepare",
            "format selected Python or Markdown files with locked tools, without builds"),
    Command("test", "toolchain.cli.test",
            "the HoldFast toolchain's behavioral tests"),
    Command("holdfast", "toolchain.cli.holdfast",
            "check, format, and lint pure HoldFast source or emit Gallina"),
    Command("holdfast-borrow-compare", "toolchain.cli.holdfast_borrow_compare",
            "replay pinned Rust and optional Ante borrow decisions and observation tests"),
    Command("holdfast-copy-trial", "toolchain.cli.holdfast_copy_trial",
            "replay the frozen copy-service trial observations with a native C compiler"),
    Command("holdfast-lsp", "toolchain.cli.holdfast_lsp",
            "serve pure HoldFast over stdio or run pinned LSP client qualification"),
    Command("holdfast-highlight", "toolchain.cli.holdfast_highlight",
            "generate and qualify syntax-only Tree-sitter and TextMate editor assets",
            lane="guest", host_ok=frozenset({"check", "generate", "--help", "-h"})),
    Command("holdfast-playground", "toolchain.cli.holdfast_playground",
            "serve the unified HoldFast browser editor with dependent mathematics", lane="guest"),
    Command("holdfast-parser", "toolchain.cli.holdfast_parser",
            "parse HoldFast, elaborate dependent mathematics and replay proofs", lane="guest"),
)

BY_NAME: dict[str, Command] = {command.name: command for command in COMMANDS}
