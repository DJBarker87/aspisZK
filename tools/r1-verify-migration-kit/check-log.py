#!/usr/bin/env python3
"""Check complete coverage of one actual-S2 verify injection log; no execution."""
import argparse
import re
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("log", type=Path)
ap.add_argument("--detail", choices=["true", "false"], required=True)
args = ap.parse_args()
text = args.log.read_text()
faults = ["None", "Parse", "Public", "Begin", "Lookup(14, 0)", "Decode(14)"]
for row in range(15, 25):
    faults += [f"Lookup({row}, 0)", f"Decode({row})", f"Boundary({row})",
               f"Lookup({row}, 1)", f"Semantic({row})"]
pattern = re.compile(r"^VERIFY_REAL_S2_CASE fault=(.*?) observed=(true|false) "
    r"detail_phases=(true|false) old_new_equal=true error=(.*?) digest_calls=(\d+) "
    r"trace_values=(\d+) events=(\d+) phases=(\d+) full_outcome_sha256=\[([^\]]+)\]$", re.M)
matches = pattern.findall(text)
assert len(matches) == 112, f"Expected112 complete per-case lines, got{len(matches)}"
seen = set()
for fault, observed, detail, error, digests, values, events, phases, digest in matches:
    assert fault in faults and detail == args.detail
    assert (fault, observed) not in seen
    seen.add((fault, observed))
    assert len(re.findall(r"[0-9a-f]{2}", digest)) == 32
    if fault == "None":
        expected_error, expected_digests = "None", 82
    elif fault == "Public":
        expected_error, expected_digests = "Some(Public)", 0
    elif fault == "Begin":
        expected_error, expected_digests = "Some(RowOrder { expected: 0, actual: 1 })", 1
    elif fault == "Parse" or fault.startswith("Lookup"):
        expected_error = "Some(InvalidRow)"
        expected_digests = 0 if fault == "Parse" else 46 + 3 * max(0, int(re.search(r"\d+", fault)[0]) - 15)
    else:
        row = int(re.search(r"\d+", fault)[0])
        expected_digests = 46 + 3 * max(0, row - 15)
        if fault.startswith("Decode"):
            expected_error = f"Some(NonCanonical {{ row: {row}, value: 0 }})"
        elif fault.startswith("Boundary"):
            expected_error = f"Some(Boundary {{ round: {row - 15} }})"
        else:
            expected_error = f"Some(RowOrder {{ expected: {row}, actual: {row + 1} }})"
    assert error == expected_error, (fault, error, expected_error)
    assert int(digests) == expected_digests, (fault, digests, expected_digests)
    assert int(values) == (61 if fault == "None" else 0), (fault, values)
    if detail == "false" or observed == "false":
        assert int(phases) == 0
    else:
        assert int(phases) == (6 if fault == "None" else 0 if fault == "Parse" else 1 if fault in ["Public", "Begin"] else 2)
assert seen == {(f, o) for f in faults for o in ["false", "true"]}
assert f"VERIFY_REAL_S2_PASS cases=112 faults=55 rows=14..24 observers=Some,None detail_phases={args.detail}" in text
assert "test result: ok." in text
print(f"PASS:112 actual-S2 cases, all55 fault points, both observers, detail={args.detail}, exact errors/digest counts/trace counts/phases")
