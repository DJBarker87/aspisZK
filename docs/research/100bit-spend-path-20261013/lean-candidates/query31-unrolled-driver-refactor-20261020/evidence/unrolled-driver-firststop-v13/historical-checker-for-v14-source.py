#!/usr/bin/env python3
"""Check source declarations copied into the no-Funs first-stop proof."""

from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
GENERATED = HERE.parent / "unrolled-driver-firststop-v12/generated/AspisR1Query31Transcript/Funs.lean"
SOURCE = HERE / "Query31UnrolledDriverFirstStop.lean"
EXPECTED_GENERATED_SHA = "d192f7291571583454e7758fabcfde32f7f6df965e4bd9e4d90a0bf76b67d9c5"
EXPECTED_SOURCE_SHA = "ea5c3cb0449e09d7c12f8b98adf7fbc2be19137ca4f64f6122bc879689a7597b"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def generated_decl(name: str) -> str:
    text = GENERATED.read_text()
    definition = text.index("def " + name)
    if "QUERY_" in name:
        start = text.rfind("\n@[global_simps, irreducible]", 0, definition) + 1
    else:
        start = definition
    end = text.index("\n/--", definition)
    return text[start:end].rstrip()


def local_decl(text: str, name: str) -> str:
    definition = text.index("def " + name)
    if "QUERY_" in name:
        start = text.rfind("\n@[global_simps, irreducible]", 0, definition) + 1
    else:
        start = definition
    if name.endswith("QUERY_COUNT"):
        end = text.index("\n\n@[global_simps, irreducible]", definition)
    elif name.endswith("QUERY_MAX_DRAWS"):
        end = text.index("\ndef aspis_core.r0_transcript.QueryScan.finish", definition)
    else:
        end = text.index("\n\nprivate theorem bind_success", definition)
    return text[start:end].rstrip()


def main() -> int:
    text = SOURCE.read_text()
    if digest(GENERATED) != EXPECTED_GENERATED_SHA:
        print("generated normalized Funs source hash mismatch", file=sys.stderr)
        return 1
    if digest(SOURCE) != EXPECTED_SOURCE_SHA:
        print("first-stop source hash mismatch", file=sys.stderr)
        return 1
    if "import AspisR1Query31Transcript.Funs" in text or "import AspisR1Query31Transcript.FunsExternal" in text:
        print("forbidden generated Funs import", file=sys.stderr)
        return 1
    for name in (
        "aspis_core.r0_transcript.QUERY_COUNT",
        "aspis_core.r0_transcript.QUERY_MAX_DRAWS",
        "aspis_core.r0_transcript.QueryScan.finish",
    ):
        if generated_decl(name) != local_decl(text, name):
            print(f"copied declaration differs from generated source: {name}", file=sys.stderr)
            return 1

    raw_start = GENERATED.read_text().index("def aspis_core.r0_transcript.queries_from_pairs\n")
    raw_text = GENERATED.read_text()
    raw_end = raw_text.index("\nend AspisR1Query31Transcript", raw_start)
    expected = raw_text[raw_start:raw_end].rstrip()
    actual_start = text.index("def queries_from_pairs_with_scan\n")
    actual_end = text.index("\ninductive DriverTrace", actual_start)
    actual = text[actual_start:actual_end].rstrip()
    expected = expected.replace(
        "def aspis_core.r0_transcript.queries_from_pairs\n",
        "def queries_from_pairs_with_scan\n", 1)
    expected = expected.replace(
        "  (blocks : Array (Array Std.U8 32#usize) 8#usize)\n",
        "  (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))\n"
        "  (scan0 : aspis_core.r0_transcript.QueryScan)\n"
        "  (blocks : Array (Array Std.U8 32#usize) 8#usize)\n", 1)
    expected = expected.replace(
        "  let scan ←\n"
        "    aspis_core.r0_transcript.QueryScan.Insts.CoreDefaultDefault.default\n",
        "  let scan := scan0\n", 1)
    expected = expected.replace("aspis_core.r0_transcript.QueryScan.scan scan", "scanFn scan")
    if expected != actual:
        print("driver body differs beyond scanFn/scan0 substitutions", file=sys.stderr)
        return 1
    print("PASS: no Funs import; constants/finish copied exactly; driver differs only by scanFn/scan0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
