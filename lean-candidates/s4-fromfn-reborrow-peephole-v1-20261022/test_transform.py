#!/usr/bin/env python3
"""Deterministic positive and extra-use-negative tests for the LLBC peephole."""

import json
from pathlib import Path

import transform_llbc as lower

ROOT = Path(__file__).resolve().parents[2]
INPUT = ROOT / "docs/research/100bit-spend-path-20261013/lean-candidates/s4-stdlib-fromfn-isolation-v1-20261021/remote-attempts/attempt-v2/from_fn.llbc"
EXPECTED = lower.EXPECTED_INPUT_SHA


def get_loop(fun):
    body = fun["body"]["Structured"]["body"]["statements"]
    return next(s for s in body if "Loop" in s["kind"])["kind"]["Loop"]["statements"]


def check_positive(doc):
    out, receipt = lower.transform_doc(doc)
    source_loop = get_loop(lower.target_function(doc))
    loop = get_loop(lower.target_function(out))
    expected_loop = json.loads(json.dumps(source_loop))
    removed_index = next(i for i, s in enumerate(expected_loop) if s.get("id") == receipt["copy_stmt_id"])
    removed = expected_loop.pop(removed_index)
    assert removed["kind"]["Assign"][0]["kind"] == {"Local": receipt["temporary_local"]}
    ref = next(s for s in expected_loop if s.get("id") == receipt["ref_stmt_id"])
    ref_rhs = ref["kind"]["Assign"][1]["Ref"]
    original_place = removed["kind"]["Assign"][1]["Use"][0]["Copy"]
    ref_rhs["place"]["kind"]["Projection"][0] = original_place
    ref_rhs["ptr_metadata"]["Copy"]["kind"]["Projection"][0] = original_place
    assert loop == expected_loop, "transform changed more than the one copy and two reborrow bases"
    assert not any(s.get("id") == receipt["copy_stmt_id"] for s in loop)
    ref = next(s for s in loop if s.get("id") == receipt["ref_stmt_id"])
    rvalue = ref["kind"]["Assign"][1]["Ref"]
    assert rvalue["kind"] == "Shared"
    # Preserve the shared borrow region and point both projections directly
    # through Guard.array_mut.
    assert rvalue["place"]["ty"] == {"Deduplicated": 2244}
    assert rvalue["place"]["kind"]["Projection"][0]["kind"]["Projection"][1]["Field"][1] == 0
    assert rvalue["ptr_metadata"]["Copy"]["kind"]["Projection"][0]["kind"]["Projection"][1]["Field"][1] == 0
    assert lower.contains_local(lower.target_function(out)["body"]["Structured"]["body"], receipt["temporary_local"]) == 0
    return receipt


def check_negative(doc):
    mutated = lower.add_negative_extra_use(doc)
    try:
        lower.transform_doc(mutated)
    except lower.NoMatch as exc:
        assert "occurrences, expected 3" in str(exc)
        return str(exc)
    raise AssertionError("peephole transformed a temporary with an extra use")


def candidate_copy_rvalue(doc):
    fun = lower.target_function(doc)
    statements = get_loop(fun)
    for i in range(len(statements) - 1):
        lhs, ref = statements[i], statements[i + 1]
        if lhs.get("id") == 230 and ref.get("id") == 231:
            return lhs["kind"]["Assign"][1]["Use"][0]["Copy"]
    raise AssertionError("pinned copy/ref pair not found")


def check_negative_typevar(doc):
    mutated = json.loads(json.dumps(doc))
    copied = candidate_copy_rvalue(mutated)
    # Keep the outer Ref/Mut shape, but change its exact referent type. The
    # matcher must not erase this type-variable distinction.
    copied["ty"]["HashConsedValue"][1]["Ref"][1] = {"Var": 987654}
    try:
        lower.transform_doc(mutated)
    except lower.NoMatch as exc:
        assert "candidate pattern" in str(exc)
        return str(exc)
    raise AssertionError("peephole accepted a different mutable-reference referent")


def check_negative_mutability(doc):
    mutated = json.loads(json.dumps(doc))
    copied = candidate_copy_rvalue(mutated)
    copied["ty"]["HashConsedValue"][1]["Ref"][2] = "Shared"
    try:
        lower.transform_doc(mutated)
    except lower.NoMatch as exc:
        assert "candidate pattern" in str(exc)
        return str(exc)
    raise AssertionError("peephole accepted a shared source in the mutable-ref pattern")


def main():
    assert lower.sha256(INPUT) == EXPECTED
    doc = json.loads(INPUT.read_text())
    receipt = check_positive(doc)
    rejection = check_negative(doc)
    typevar_rejection = check_negative_typevar(doc)
    mutability_rejection = check_negative_mutability(doc)
    print(json.dumps({
        "positive": receipt,
        "negative_extra_use": rejection,
        "negative_changed_referent_type": typevar_rejection,
        "negative_changed_mutability": mutability_rejection,
    }, indent=2))


if __name__ == "__main__":
    main()
