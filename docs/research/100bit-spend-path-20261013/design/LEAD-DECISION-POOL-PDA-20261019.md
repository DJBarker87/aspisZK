# User decision: Pool PDA searches (2026-10-19)

Context: `LEAD-REVIEW-CU-BOUND-20261019.md`. The pre-registered CU bound
failed mainly on `find_program_address` in `programs/aspis-pool` (up to 255
bump attempts × 1,500 CU per call, 11–14 calls per settlement).

**Decision (user): option C.** A design study first, costing
(A) keep the canonical-bump search with an explicit tail-probability rule and
(B) a search-free nullifier/page design (for example `create_with_seed`-style
derivation or nullifier pages), for CU, soundness (one valid address per
nullifier; no double-spend through a second bump), migration and Lean impact.
No choice between A and B is made until the study reports.

In the same job (lead recommendation): stored canonical bumps for the Pool
PDAs whose seeds are constant per deployment (state, vault, registry, pair
state), as G_R1.8 did for the R1 verifier, through the standing gates.
A second, tighter CU bound is pre-registered separately after the study.
