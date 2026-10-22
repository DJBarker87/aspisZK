# S4 candidate reached-call field results

This packet strengthens the candidate loop result: for each index in the ten- or twelve-query segment, it returns the actual successful call under `concreteCandidateQueryOps` and derives `QueryFieldEvidence concreteOps` for that same accumulator and coefficient array. It uses the ordered chain extracted from the successful candidate loop, transfers each reached call result to the old P6 model, then applies the existing scanner-backed field theorem.

The upstream scanner, ClaimPowers, caller-array, and start-cursor facts remain explicit. Scope is the selected Lean query model; Rust/runtime correspondence and production adoption are not claimed.

Validation: `python3 check_packet.py`; Lean 4.32.0 `-j1 -M 4400`; see the exact launch and resource receipt in `evidence/`.
