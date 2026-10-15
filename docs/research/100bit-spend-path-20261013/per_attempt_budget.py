#!/usr/bin/env python3
"""Exact conditional per-attempt arithmetic; not protocol instantiation."""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ledger_path = HERE / "security-ledger.json"
ledger = json.loads(ledger_path.read_text())
rows = {
    name: Fraction(int(value["numerator"]), int(value["denominator"]))
    for name, value in ledger["rows"].items()
}
p = int(ledger["field_p"])
assert p == 2**31 - 1
semantic_sum = 303100 * (Fraction(1, p**4) + Fraction(1, 2**256))
remaining = {k: v for k, v in rows.items() if k != "semantic_conservative_max"}
assert len(remaining) == 6
loose = 33 * max(rows.values())
summed = semantic_sum + sum(remaining.values())
target = Fraction(1, 2**100)
assert 0 < summed <= loose <= target


def describe(value):
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "negative_log2_approx": math.log2(value.denominator) - math.log2(value.numerator),
        "at_most_2_neg_100": value <= target,
    }


result = {
    "status": "conditional_arithmetic_only_not_security_theorem",
    "user_target": "100-bit per-attempt soundness, without grinding credit",
    "ledger_sha256": hashlib.sha256(ledger_path.read_bytes()).hexdigest(),
    "semantic_prefix_source_sha256": hashlib.sha256(
        (HERE / "lean" / "SemanticBudget.lean").read_bytes()
    ).hexdigest(),
    "loose_33_times_max_row": describe(loose),
    "semantic_checked_sum_plus_six_remaining_rows": describe(summed),
    "semantic_sum_coefficient": 303100,
    "no_work_or_grinding_credit": True,
    "not_included": [
        "Concrete classifier and row-law premises are not established here",
        "Hash/commitment collision and source correspondence obligations",
        "Knowledge extraction and privacy",
        "Adaptive repeated-attempt Fiat-Shamir query budget",
    ],
}
(HERE / "per-attempt-budget.json").write_text(json.dumps(result, indent=2) + "\n")
for key in ("loose_33_times_max_row", "semantic_checked_sum_plus_six_remaining_rows"):
    print(f"{key}: {result[key]['negative_log2_approx']:.9f} bits (conditional)")
