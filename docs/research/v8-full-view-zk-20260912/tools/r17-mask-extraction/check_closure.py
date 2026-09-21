#!/usr/bin/env python3
"""Authenticate the schematic closure BODY, not a source-to-model theorem."""
import argparse
import hashlib
from pathlib import Path

PIN = "e8b29608ef90d72b4dd3d8b0697f6619fb0e4896fdb475cdd8725fff4cc80fa3"
NAME = "r17_structured_g.mixing_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut"


def check_body(raw, leaf):
    generated = raw.split(NAME, 1)[1].split("  := do\n", 1)[1].split("\n\n/--", 1)[0]
    projected = leaf.split("-- SOURCE BODY:", 1)[1].split(" := do\n", 1)[1].split("\n-- END SOURCE BODY", 1)[0]
    assert generated.replace("field.QM31.mul", "mul") == projected, "closure body mismatch"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("generated", type=Path)
    parser.add_argument("leaf", type=Path)
    args = parser.parse_args()
    data = args.generated.read_bytes()
    assert hashlib.sha256(data).hexdigest() == PIN, "generated source pin mismatch"
    raw, leaf = data.decode(), args.leaf.read_text()
    check_body(raw, leaf)
    for before, after in [("(q2, q)", "(q2, q2)"), ("mul out q", "mul q out")]:
        assert before in leaf
        try:
            check_body(raw, leaf.replace(before, after, 1))
        except AssertionError:
            continue
        raise AssertionError("mutation was accepted: " + before)
    print("PASS: exact generated closure body with only mul abstraction; two mutations rejected")
    print("NOT a certificate of the full caller, runtime adapters, or compiler")


if __name__ == "__main__":
    main()
