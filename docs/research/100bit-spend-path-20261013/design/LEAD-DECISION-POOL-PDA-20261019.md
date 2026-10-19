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

## Follow-up decision (user, 2026-10-19, after the study)

B3's ≈98k worst case is too much. **Chosen: B1** (seed-derived marker
address: seed = 7-bit packing of the first 28 bytes of
SHA-256("aspis-marker-seed-v1" ‖ pool ‖ nullifier), address =
`create_with_seed(marker_authority, seed, pool_program)`; ≈360 CU fixed),
with **B4** (checkpoint by its stored bump; history pages by a 2-byte
caller-supplied bump hint checked with one `create_program_address`) and the
**vault authority / vault token account by a Pool-only bump hint** (no master
format change, so no verifier change). Freshness is restated as a release
premise with the new address function and a named collision-resistance
premise for the truncated SHA-256 (blocking only, never double spend).
