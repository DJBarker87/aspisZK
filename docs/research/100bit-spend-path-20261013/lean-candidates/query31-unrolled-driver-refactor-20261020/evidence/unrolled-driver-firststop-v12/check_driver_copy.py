#!/usr/bin/env python3
"""Check the driver definition is the generated body with only two adapters."""

from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
RAW = HERE / "generated/AspisR1Query31Transcript/Funs.lean"
ADAPTED = HERE / "Query31UnrolledDriverFirstStop.lean"
EXPECTED_RAW_SHA = "d192f7291571583454e7758fabcfde32f7f6df965e4bd9e4d90a0bf76b67d9c5"
EXPECTED_ADAPTED_SHA = "00847b99888fbca344fe009894ac56cf29cee524c2d2b23e336e19dbcab9d89f"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def main() -> int:
    raw_text = RAW.read_text()
    adapted_text = ADAPTED.read_text()
    raw_start = raw_text.index("def aspis_core.r0_transcript.queries_from_pairs\n")
    raw_end = raw_text.index("\nend AspisR1Query31Transcript", raw_start)
    expected = raw_text[raw_start:raw_end].rstrip()

    actual_start = adapted_text.index("def queries_from_pairs_with_scan\n")
    actual_end = adapted_text.index("\ninductive DriverTrace", actual_start)
    actual = adapted_text[actual_start:actual_end].rstrip()

    expected = expected.replace(
        "def aspis_core.r0_transcript.queries_from_pairs\n",
        "def queries_from_pairs_with_scan\n",
        1,
    )
    expected = expected.replace(
        "  (blocks : Array (Array Std.U8 32#usize) 8#usize)\n",
        "  (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))\n"
        "  (scan0 : aspis_core.r0_transcript.QueryScan)\n"
        "  (blocks : Array (Array Std.U8 32#usize) 8#usize)\n",
        1,
    )
    expected = expected.replace(
        "  let scan ←\n"
        "    aspis_core.r0_transcript.QueryScan.Insts.CoreDefaultDefault.default\n",
        "  let scan := scan0\n",
        1,
    )
    expected = expected.replace(
        "aspis_core.r0_transcript.QueryScan.scan scan", "scanFn scan"
    )

    if digest(RAW) != EXPECTED_RAW_SHA:
        print("sanitized generated owner hash mismatch", file=sys.stderr)
        return 1
    if digest(ADAPTED) != EXPECTED_ADAPTED_SHA:
        print("adapted theorem source hash mismatch", file=sys.stderr)
        return 1
    if expected != actual:
        print("driver definition differs beyond the two recorded substitutions", file=sys.stderr)
        return 1
    print("PASS: exact generated driver body; only scan callback and initial state are injected")
    print(f"generated_driver_body_bytes={len(expected.encode())}")
    print(f"adapted_driver_body_bytes={len(actual.encode())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
