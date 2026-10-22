# S9 candidate body evidence and high-array canonicality

This source-only packet combines the actual generated-body success decomposition with the high-array canonicality theorem. `candidate_body_success_evidence` exposes the exact ordered powers and `scalar_factor` results from one successful candidate body call. `candidate_high_array_canonical` proves canonicality of each mapped high-array entry from the seed canonicality and the corresponding operation-result witnesses.

The two Lean targets were compiled at separate source revisions; each launch receipt records its own revision. Their external `.olean` files are pinned by path and SHA and are not included. The high-array target was compiled against the body-evidence producer and its complete selected import closure. The body producer’s immediate parent is the accepted `s9-candidate-body-prefix-terms-v1-20261022` packet.

This packet does not establish scalar-fold transport, full helper closure, or Rust standard-library `from_fn` correspondence. Run `python3 check_packet.py` to validate the source/object pins, receipts, axiom reports, dependency closure, and source-only packaging.
