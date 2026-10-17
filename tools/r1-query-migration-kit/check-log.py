#!/usr/bin/env python3
"""Independently check coverage, real SHA answers and traces in the query log."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("log", type=Path)
args = ap.parse_args()
text = args.log.read_text()
records = [json.loads(line.split("QUERY_MIGRATION_CASE ", 1)[1])
    for line in text.splitlines() if "QUERY_MIGRATION_CASE " in line]
faults = ["None", *[f"Abort({i})" for i in range(1, 17)],
          *[f"Alter({i})" for i in range(1, 17)], "Decoder"]
contexts = ["saved-S2", "synthetic-S1", "synthetic-D"]
assert len(records) == 102
seen = set()
for record in records:
    context, fault = record["context"], record["fault"]
    assert context in contexts and fault in faults
    assert (context, fault) not in seen
    seen.add((context, fault))
    events, trace = record["events"], record["trace"]
    position = int(re.search(r"\d+", fault)[0]) if "(" in fault else None
    for i, event in enumerate(events):
        if fault.startswith("Abort") and i == position:
            assert event["answer"] is None
            continue
        actual = hashlib.sha256(b"".join(bytes(part) for part in event["parts"])).digest()
        if fault.startswith("Alter") and i == position:
            actual = bytes([actual[0] ^ 0x80]) + actual[1:]
        assert bytes(event["answer"]) == actual, (context, fault, i)
    if fault.startswith("Abort"):
        assert record["abort"] == position and record["result"] == "None"
        assert len(events) == position + 1 and not trace
        assert record["decoder"] == "[]"
        assert record["state"] == events[0]["answer"]
    else:
        assert record["abort"] is None and len(events) == 17
        if fault == "Decoder":
            assert record["result"] == "Some(Err(Transcript))" and not trace
            assert record["state"] == events[0]["answer"]
        elif record["result"].startswith("Some(Ok(["): 
            numbers = record["result"].removeprefix("Some(Ok([").removesuffix("]))")
            queries = [int(x.strip()) for x in numbers.split(",")]
            assert len(queries) == len(trace) == 22
            for i, q in enumerate(queries):
                assert 0 <= q < 262144
                assert trace[i] == [5, i, list(q.to_bytes(4, "little") + bytes(28))]
        else:
            assert fault.startswith("Alter")
            assert record["result"] == "Some(Err(Transcript))" and not trace
    if fault == "None":
        assert record["result"].startswith("Some(Ok([")
assert seen == {(c, f) for c in contexts for f in faults}
assert "QUERY_MIGRATION_PASS cases=102 contexts=3 digest_abort_cases=48 altered_digest_cases=48 decoder_errors=3 success_controls=3 trace_indices=0..21" in text
assert "test result: ok." in text
print("PASS:102 cases; all16 digest positions; real SHA/one-bit alterations; abort/error carry; all22 exact trace values")
