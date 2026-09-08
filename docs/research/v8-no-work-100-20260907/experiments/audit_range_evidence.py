#!/usr/bin/env python3
"""Read-only check of retained CU rows, body census, and proof-byte hashes."""
import json
from pathlib import Path
root=Path(__file__).resolve().parent.parent
r=json.loads((root/"range-performance-results.json").read_text())
assert sum(r["wire_terms"].values())==r["max_body_bytes"]==40282
assert r["overflow_checks"] and r["full_transaction_cu"] is None
for mode in r["modes"]:
    rows=[json.loads(x) for x in (root/"evidence"/mode["evidence"]).read_text().splitlines() if x.startswith("{")]
    assert mode["cu"]==[x["cu"] for x in rows if x["case"]=="honest" and x["cu_limit"]==100000000]
for name in ["range-final-svm.log","range-max-svm.log","range-max-profile-svm.log"]:
    rows=[json.loads(x) for x in (root/"evidence"/name).read_text().splitlines() if x.startswith("{")]
    assert len(rows)==36, (name,len(rows))
    assert all(x["unchanged_accounts"] for x in rows)
    assert all(x["accepted"] and x["cu"]<1200000 for x in rows if x["case"]=="honest")
    bad=[x for x in rows if x["case"]!="honest"]
    assert len(bad)==27 and all(not x["accepted"] and "Custom(" in x["error"] for x in bad)
def proof_hashes(name,part):
    return [x.split()[0] for x in (root/"evidence"/name).read_text().splitlines() if part in x and "/proof-" in x]
assert proof_hashes("range-final-hashes.txt","fixture-structured-v2")==proof_hashes("range-ordinary-hashes.txt","fixture-range-ordinary")
print("range evidence: exact census, CU rows, 27 checked negatives per final corpus, unchanged ordinary proof bytes: PASS")
