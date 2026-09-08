#!/usr/bin/env python3
"""Check recorded measurements/census, not cryptographic soundness."""
import json
from pathlib import Path
root = Path(__file__).resolve().parent.parent
data = json.loads((root / "performance-results.json").read_text())
wire = data["wire"]
assert wire["max_body_bytes"] == 697*16 + 52 + 24 + 22*621 + 2*296*26 == 40282
assert all(n <= 40282 for n in wire["observed_body_bytes"])
rows = [json.loads(s) for s in (root / "evidence/performance-svm-selected.log").read_text().splitlines() if s.startswith("{")]
assert rows == data["sbf"]["rows"]
assert len(rows) == 18
for row in rows:
    assert row["unchanged_accounts"]
    if row["cu_limit"] == 1_400_000:
        assert row["case"] == "honest" and not row["accepted"]
        assert row["cu"] == 1_400_000
    elif row["case"] == "honest":
        assert row["accepted"] and row["cu"] > 1_400_000
    else:
        assert not row["accepted"] and "Custom(" in row["error"]
assert data["sbf"]["full_transaction_cu"] is None
assert data["sbf"]["matched_v7_cu"] is None
assert data["host"]["grinding_attempts"] == 0
assert data["host"]["prover_seconds"]["tail_claim"] is None
print("PASS: 18 measured SVM outcomes, 40,282-byte census, no fabricated full-CU or tail result")
