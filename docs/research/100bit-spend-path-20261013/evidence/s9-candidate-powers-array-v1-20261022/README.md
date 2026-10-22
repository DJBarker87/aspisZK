# S9 candidate explicit powers array bridge

This source-only packet records the focused theorem
`AspisR1S9CandidateExplicitPowersArrayBridgeV1.candidate_explicit_powers4_matches_p6`.
For a canonical seed and the candidate's first three successful multiplications,
it identifies the explicit candidate array `[ONE, q1, q2, q3]` with the
successful retained P6 `kpowers` output under the mapped seed. It preserves the
candidate's fourth multiplication as `hmul4` in the theorem input to document
the source call schedule; the array equality does not consume that premise.
The theorem does not identify Rust `from_fn` with the P6 model or discharge the
frozen standard-library boundary.

The accepted target was Lean 4.32, exit 0, 34.137 seconds, maximum process RSS
2,597,896,192 bytes, zero swap, with named axioms `[propext, Classical.choice,
Quot.sound]`. Exact source/object hashes, direct imported owners and the selected
profile are recorded in the manifest and `evidence/`. The compiled object is not
included.

The original run used the retained controller at `run_focused.py` (SHA
`3334b7d099553e981d55183c9d78cca42fe850fc2b53aab965cf916b4d37d0ee`). Exact
concurrency observations are preserved in `evidence/concurrency-observations.json`.
`python3 -B check_packet.py` verifies the retained source and run evidence.
