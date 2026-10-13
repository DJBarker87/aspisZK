#!/usr/bin/env python3
"""Recompute the published phase table directly from the four raw receipts."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TABLE = json.loads((ROOT / "P2-CU-RECONCILIATION.json").read_text())
BUCKET = {
    "parsed": "Parse",
    "semantic": "Semantic",
    "semantic-part": "Semantic",
    "prepare": "Prepare",
    "checkpoint-read": "Checkpoint read",
    "merkle": "Merkle",
    "query": "Query folds and rho accumulation",
    "query-part": "Query folds and rho accumulation",
    "relation": "Relation rounds and pairing",
    "final": "Final rho evaluation",
    "checkpoint-write": "Checkpoint write",
    "account-write": "Checkpoint write",
}
for tx in (1, 2):
    for stage in ("p2", "pairing"):
        raw = json.loads((ROOT / "evidence/p2-cu-reconciliation" /
                          f"{stage}-transfer-tx{tx}.json").read_text())
        expected = TABLE["phase_comparison"][str(tx)][stage]
        actual = dict.fromkeys(BUCKET.values(), 0)
        markers = raw["phase_markers"]
        assert markers[0]["phase"] == "begin"
        for before, after in zip(markers, markers[1:]):
            delta = before["remaining_cu"] - after["remaining_cu"]
            assert delta >= 0
            actual[BUCKET[after["phase"].split(":")[0]]] += delta
        actual["Entry/exit and other overhead"] = raw["verifier_cu"] - sum(actual.values())
        actual["Program subtotal CU"] = raw["verifier_cu"]
        actual["Other transaction overhead CU"] = raw["execution"]["cu"] - raw["verifier_cu"]
        actual["Total transaction CU"] = raw["execution"]["cu"]
        assert actual == expected, (stage, tx, actual, expected)
    phases = TABLE["phase_comparison"][str(tx)]
    assert phases["p2_minus_pairing"] == {
        k: v - phases["pairing"][k] for k, v in phases["p2"].items()
    }
print("All P2/pairing phases, subtotals, transaction totals and savings match raw receipts.")
