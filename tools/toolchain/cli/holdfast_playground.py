# SPDX-License-Identifier: Apache-2.0
"""Serve HoldFast's local browser editor and bounded compile-time expression console."""

import argparse
import sys
from pathlib import Path

from filelock import Timeout

from toolchain import parser as holdfast_parser
from toolchain.playground import PlaygroundServer


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(suggest_on_error=True, description=__doc__)
    parser.add_argument("--port", type=int, default=8765,
                        help="IPv4 loopback port (default: 8765; zero selects an available port)")
    args = parser.parse_args(argv)
    if not 0 <= args.port <= 65535:
        parser.error("port must be between 0 and 65535")
    try:
        print("Preparing the locked HoldFast parser in this native lane...", flush=True)
        with (holdfast_parser.cached_build(Path(__file__).resolve().parents[3]) as compiled,
              PlaygroundServer(args.port, mathematical_parser=compiled.executable) as server):
            print(f"HoldFast playground: {server.launch_url}", flush=True)
            print("HoldFast functions, dependent types and proofs. Ctrl+C stops the local service.", flush=True)
            server.serve_forever()
    except KeyboardInterrupt:
        return 0
    except (OSError, RuntimeError, ValueError, Timeout) as error:
        print(f"HoldFast playground unavailable: {error}", file=sys.stderr)
        return 1
    return 0
