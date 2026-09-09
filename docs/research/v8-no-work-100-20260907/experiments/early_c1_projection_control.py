#!/usr/bin/env python3
"""Exact tiny classifier falsifier, not a proof-acceptance experiment.

An absent all-lane near-code tuple need not imply failure to recover the
semantic projection. Exhaust all constant-code tuples for one fixed F7 word.
No random trial, witness, root, query schedule or security estimate is used.
"""
import json


def main():
    field, size, cutoff = 7, 12, 2
    semantic = [5] * size
    helper = [1] * 3 + [0] * 9
    tuples = [
        (a, b, sum(x != a or y != b for x, y in zip(semantic, helper)))
        for a in range(field)
        for b in range(field)
    ]
    near = [t for t in tuples if t[2] <= cutoff]
    recovered_semantic = [a for a in range(field) if all(x == a for x in semantic)]
    assert not near
    assert min(t[2] for t in tuples) == 3
    assert recovered_semantic == [5]
    # Symbolic selected-code implication given the proved 256-fibre overlap
    # cap. These integers do not assert that a real proof was constructed.
    domain, overlap, changed, allowed = 262144, 256, 16536, 16535
    other_distance_lower = domain - overlap - changed
    assert changed > allowed and other_distance_lower > allowed
    print(json.dumps({
        "scope": "constant-code classifier only; no actual-verifier acceptance claim",
        "field": field, "fibres": size, "cutoff": cutoff,
        "tuples_exhausted": len(tuples), "all_lane_near_candidates": near,
        "semantic_candidates": recovered_semantic, "minimum_all_lane_distance": 3,
        "selected_conditional_geometry": {
            "changed_mask_only_fibres": changed,
            "all_lane_allowed_bad_fibres": allowed,
            "distinct_mask_codeword_distance_lower": other_distance_lower,
            "semantic_projection_unchanged": True,
            "source_fixture_executed": False,
        },
    }, indent=2))


if __name__ == "__main__":
    main()
