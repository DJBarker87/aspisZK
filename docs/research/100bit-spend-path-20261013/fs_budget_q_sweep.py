#!/usr/bin/env python3
"""Exact conditional arithmetic sweep varying only the q hypergeometric term.

No protocol or security premise is evaluated here.  This uses the frozen
ledger rows, retains every non-query row, and changes only q in
257*P^8/2^256 * C(9557,q)/C(262144,q).
"""
from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEDGER_PATH = ROOT / "security-ledger.json"
LEDGER_FORMULA_PATH = ROOT / "security_ledger.py"
PROFILE_FORMULA_PATH = ROOT / "fs_budget_profile.py"
OUTPUT_PATH = ROOT / "fs-budget-q-sweep.json"
Q_VALUES = range(22, 41)
Q_TOTALS = (2**20, 2**32, 2**40, 2**64)
TARGET = Fraction(1, 2**100)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_fraction(row: dict[str, str]) -> Fraction:
    return Fraction(int(row["numerator"]), int(row["denominator"]))


def fraction_object(value: Fraction) -> dict[str, str | float]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "negative_log2_approx": math.log2(value.denominator) - math.log2(value.numerator),
    }


def main() -> None:
    ledger = json.loads(LEDGER_PATH.read_text())
    rows = {name: read_fraction(row) for name, row in ledger["rows"].items()}
    p = int(ledger["field_p"])
    h = 2**256
    e = p**8
    assert p == 2**31 - 1
    assert ledger["query_count"] == 22
    assert ledger["max_row"] == "query22_existing_envelope"

    query22_formula = Fraction(257 * e, h) * Fraction(
        math.comb(9557, 22), math.comb(262144, 22)
    )
    assert rows["query22_existing_envelope"] == query22_formula

    fixed_rows = {name: value for name, value in rows.items() if name != "query22_existing_envelope"}
    fixed_max_name = max(fixed_rows, key=fixed_rows.get)
    fixed_max = fixed_rows[fixed_max_name]

    q_entries = []
    for q in Q_VALUES:
        q_row = Fraction(257 * e, h) * Fraction(math.comb(9557, q), math.comb(262144, q))
        max_row_name = max((*fixed_rows.keys(), "query_q"), key=lambda name: q_row if name == "query_q" else fixed_rows[name])
        max_row = q_row if max_row_name == "query_q" else fixed_rows[max_row_name]
        q_entries.append({
            "q": q,
            "query_row": fraction_object(q_row),
            "max_row_name": max_row_name,
            "max_row": fraction_object(max_row),
            "by_Q": [],
        })
        for Q in Q_TOTALS:
            linear = Q * max_row
            collision = Fraction(3 * Q * Q, h)
            total = linear + collision
            q_entries[-1]["by_Q"].append({
                "Q": Q,
                "Q_times_max_row": fraction_object(linear),
                "collision_3Q2_over_2_256": fraction_object(collision),
                "total": fraction_object(total),
                "at_most_2_neg_100": total <= TARGET,
            })

    by_q = {entry["q"]: entry for entry in q_entries}
    assert by_q[22]["max_row_name"] == "query_q"
    assert by_q[23]["max_row_name"] == fixed_max_name
    assert by_q[23]["max_row"] == fraction_object(fixed_max)
    assert read_fraction(by_q[23]["max_row"]) < read_fraction(by_q[22]["max_row"])
    assert all(by_q[q]["max_row"] == fraction_object(fixed_max) for q in range(23, 41))
    assert all(not result["at_most_2_neg_100"] for entry in q_entries for result in entry["by_Q"])

    out = {
        "status": "conditional_exact_arithmetic_only",
        "source_revision": "eac8ca7d792be9438200ec839b30102a5204881d",
        "input_sha256": {
            "security-ledger.json": sha256(LEDGER_PATH),
            "security_ledger.py": sha256(LEDGER_FORMULA_PATH),
            "fs_budget_profile.py": sha256(PROFILE_FORMULA_PATH),
        },
        "assumptions": {
            "varied_term": "257*P^8/2^256 * C(9557,q)/C(262144,q)",
            "all_non_query_ledger_rows_unchanged": True,
            "collision_term_unchanged": "3*Q^2/2^256",
            "target": "2^-100",
            "Q_values_are_scenarios_not_measured_query_bounds": True,
            "no_protocol_or_security_premises_evaluated": True,
        },
        "fixed_rows": {name: fraction_object(value) for name, value in fixed_rows.items()},
        "fixed_max_row_name": fixed_max_name,
        "fixed_max_row": fraction_object(fixed_max),
        "q22_equals_frozen_ledger_query_row": True,
        "q23_strictly_improves_over_q22_then_fixed_row_saturates": True,
        "sweep": q_entries,
    }
    OUTPUT_PATH.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()
