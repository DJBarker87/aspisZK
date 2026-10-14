#!/usr/bin/env python3
"""Reproduce conditional exact-rational FS budget profiles.

This script reads the frozen arithmetic ledger and the semantic row budget.
It does not instantiate protocol premises or estimate an actual failure rate.
"""
from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEDGER_PATH = ROOT / "security-ledger.json"
SEMANTIC_PATH = ROOT / "lean" / "SemanticBudget.lean"
OUTPUT_PATH = ROOT / "fs-budget-profile.json"
SOURCE_BASE = "a9d4c4bee5e2cf34ac91056b9e9a7a7ab4e1643f"
Q_SCENARIOS = [1, 2, 16, 32, 35, 36, 64, 256, 1024, 2**20, 2**32, 2**64]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def as_fraction(row: dict[str, str]) -> Fraction:
    return Fraction(int(row["numerator"]), int(row["denominator"]))


def describe(value: Fraction) -> dict[str, str | float]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "negative_log2_approx": math.log2(value.denominator) - math.log2(value.numerator),
    }


def budget(q: int, max_row: Fraction, h: int) -> Fraction:
    return q * max_row + Fraction(3 * q * q, h)


def largest_q_at_target(max_row: Fraction, h: int) -> int:
    target = Fraction(1, 2**100)
    lo, hi = 0, 1
    while budget(hi, max_row, h) <= target:
        lo, hi = hi, hi * 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if budget(mid, max_row, h) <= target:
            lo = mid
        else:
            hi = mid
    assert budget(lo, max_row, h) <= target
    assert budget(lo + 1, max_row, h) > target
    return lo


def main() -> None:
    ledger = json.loads(LEDGER_PATH.read_text())
    rows = {name: as_fraction(row) for name, row in ledger["rows"].items()}
    max_row = max(rows.values())
    assert ledger["field_p"] == 2**31 - 1
    assert ledger["max_row"] == "query22_existing_envelope"
    assert max_row == rows[ledger["max_row"]]
    assert max_row > 0

    h = 2**256
    p = 2**31 - 1
    semantic_atom = Fraction(1, p**4) + Fraction(1, h)
    semantic_max = 435200 * semantic_atom
    semantic_lean_max = 217600 * semantic_atom
    semantic_budget_sum = 303100 * semantic_atom
    qmax = largest_q_at_target(max_row, h)
    target = Fraction(1, 2**100)

    out = {
        "status": "conditional_arithmetic_only_protocol_premises_unresolved",
        "source_base_revision": SOURCE_BASE,
        "input_sha256": {
            "security-ledger.json": sha256(LEDGER_PATH),
            "lean/SemanticBudget.lean": sha256(SEMANTIC_PATH),
        },
        "scope_note": (
            "B(Q) is the root-specified conditional arithmetic expression. "
            "It is not an actual failure probability, does not include complete "
            "additional Merkle charges, and does not establish its protocol premises. "
            "The Q scenarios are arithmetic scenarios, not measured or selected budgets."
        ),
        "formula": "B(Q) = Q * max(rows in security-ledger.json) + 3 * Q^2 / 2^256",
        "max_row_name": ledger["max_row"],
        "max_row_exact": describe(max_row),
        "query_count_in_source_ledger": ledger["query_count"],
        "q_scenarios": [
            {"Q": q, "B_exact": describe(budget(q, max_row, h))}
            for q in Q_SCENARIOS
        ],
        "q_limit_for_2_neg_100_arithmetic_target": {
            "target_exact": "1/1267650600228229401496703205376",
            "largest_integer_Q": qmax,
            "at_Q_exact": describe(budget(qmax, max_row, h)),
            "at_Q_le_target": budget(qmax, max_row, h) <= target,
            "next_Q": qmax + 1,
            "at_next_Q_exact": describe(budget(qmax + 1, max_row, h)),
            "next_Q_gt_target": budget(qmax + 1, max_row, h) > target,
        },
        "semantic_budget_descriptive_only": {
            "P": p,
            "H": h,
            "atom_formula": "1/P^4 + 1/2^256 = (1 + P^4/2^256)/P^4",
            "retained_conservative_ledger_row_435200": describe(semantic_max),
            "SemanticBudget_lean_max_217600": describe(semantic_lean_max),
            "SemanticBudget_lean_sum_303100": describe(semantic_budget_sum),
            "note": (
                "Both are displayed separately. This script does not replace the "
                "security-ledger.json semantic_conservative_max row."
            ),
        },
    }
    OUTPUT_PATH.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()
