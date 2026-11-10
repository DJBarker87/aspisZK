# PCXD_NONFROZEN: the 26 non-frozen cone modules

Target not yet established. Source: PCUH_NONFROZEN_STATUS.json refreshed from PCUJ_ALL_STATUS.json. A module is ALL_DEFINITIONS_EQUALITY_PROVED only when every definition has an equality against a fresh frozen extraction; detector-blind modules are UNVERIFIED until then.

Verdicts: {'UNVERIFIED': 21, 'ALL_DEFINITIONS_EQUALITY_PROVED': 4, 'OPEN': 1}. Definition statuses: {'HAND_ADAPTED': 11, 'EQUALITY_PROVED': 231, 'OPEN': 89, 'EQUALITY_DOMAIN': 4, 'NO_FROZEN_COUNTERPART': 4, 'UNVERIFIED_RECEIPTED_ONLY': 1, 'RECEIPTED': 3}. 26 of 26 are in the deployed_splitB cone. 8 gate definitions have no frozen counterpart.

| module | splitB | verdict | source blob | frozen counterpart(s) | definitions |
|---|---|---|---|---|---|
| AdapterRwModel | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs | {'HAND_ADAPTED': 4, 'EQUALITY_PROVED': 12, 'OPEN': 17} |
| AspisR1AdapterReconstruct.Funs | yes | ALL_DEFINITIONS_EQUALITY_PROVED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-statement/src/atomic_statement.rs; crates/aspis-statement/src/pool_v1/pair_fo | {'EQUALITY_PROVED': 4} |
| AspisR1AdapterReconstruct.Types | yes | ALL_DEFINITIONS_EQUALITY_PROVED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs; programs/adapter-reconstruct/l | {'EQUALITY_PROVED': 4} |
| AspisR1DecodeKFullV10.Funs | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/r1_wire.rs | {'OPEN': 4, 'EQUALITY_PROVED': 1} |
| AspisR1TerminalDecoder.Funs | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-statement/src/atomic_statement.rs; crates/aspis-statement/src/pool_v1/pair_fo | {'EQUALITY_PROVED': 41, 'EQUALITY_DOMAIN': 4, 'OPEN': 12} |
| AspisR72Sampler.Funs | yes | OPEN | a47a9996aa63c4b368a6007f4a597fdd3636c756 | crates/aspis-core/src/field.rs; crates/aspis-core/src/r23_width.rs; crates/aspis-core/src/ | {'EQUALITY_PROVED': 35, 'OPEN': 1, 'NO_FROZEN_COUNTERPART': 4} |
| AspisR72Sampler.Types | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-core/src/field.rs; crates/aspis-core/src/transcript.rs | {'OPEN': 2, 'EQUALITY_PROVED': 4} |
| ClaimsUnrolledParentSource | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/candidate_claims.rs | {'OPEN': 2} |
| CurrentCompactCallerTypesV1 | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-core/src/state_only_prefix.rs | {'EQUALITY_PROVED': 10, 'OPEN': 8} |
| NFN_ExtractedGeometry | yes | ALL_DEFINITIONS_EQUALITY_PROVED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-core/src/field.rs; crates/aspis-core/src/r0/domain.rs; crates/aspis-r1-cost-p | {'EQUALITY_PROVED': 25} |
| NFY_Part043 | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs | {'EQUALITY_PROVED': 23, 'OPEN': 2} |
| NGN_Emitted | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/lib.rs | {'EQUALITY_PROVED': 2, 'OPEN': 1} |
| NJA_CountBody | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/multiproof.rs | {'OPEN': 2, 'EQUALITY_PROVED': 5} |
| NJC_ValidateEmission | yes | ALL_DEFINITIONS_EQUALITY_PROVED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'EQUALITY_PROVED': 3} |
| NJS_Extract.Funs | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/candidate.rs | {'EQUALITY_PROVED': 33, 'OPEN': 15} |
| NJT_ClaimsRef_Funs | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/r1_semantic.rs | {'OPEN': 1} |
| Port3_NativeBatchBody | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/candidate.rs | {'OPEN': 5} |
| Port3_NativeGeometryBody | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'HAND_ADAPTED': 5} |
| Port3_NativePendingBody | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'UNVERIFIED_RECEIPTED_ONLY': 1} |
| Port3_NativeQueryBody | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs; crates/aspis-r1-cost-probe/src/candidate.rs | {'RECEIPTED': 2} |
| Port4C_NativePrefix | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'RECEIPTED': 1} |
| Port5Q2_ReaderValidate | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'OPEN': 2} |
| Port5Q2_ReaderWeights | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/verifier.rs | {'HAND_ADAPTED': 2} |
| RPz7_FIo_NativeFuns | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-core/src/field.rs; crates/aspis-core/src/r0/transport.rs; crates/aspis-r1-cos | {'OPEN': 6, 'EQUALITY_PROVED': 20} |
| RPz7_FIp_NativeDots | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/fast_dots.rs | {'OPEN': 6} |
| S1NativeCompactModelV1 | yes | UNVERIFIED | NOT_IDENTIFIED (no history blob matches all detector ranges) | crates/aspis-r1-cost-probe/src/compact.rs | {'EQUALITY_PROVED': 9, 'OPEN': 3} |

## Gate definitions with NO_FROZEN_COUNTERPART

* AspisR1DecodeKFullV10.Funs: `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value` (OPEN): no function decode_k_value anywhere in frozen 4bb3b3f crates/ or programs/ (gate-only helper)
* AspisR72Sampler.Funs: `AspisR72Sampler.field.r23_product_u32_bounded` (NO_FROZEN_COUNTERPART): gate-only helper; behaviour proved (P3b), no frozen function to equate
* AspisR72Sampler.Funs: `AspisR72Sampler.field.r24_canonical_mul` (NO_FROZEN_COUNTERPART): gate-only helper; behaviour proved (P3b), no frozen function to equate
* AspisR72Sampler.Funs: `AspisR72Sampler.field.r24_canonical_mul.PP` (NO_FROZEN_COUNTERPART): gate-only helper; behaviour proved (P3b), no frozen function to equate
* AspisR72Sampler.Funs: `AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call` (NO_FROZEN_COUNTERPART): gate-only helper; behaviour proved (P3b), no frozen function to equate
* AspisR72Sampler.Types: `AspisR72Sampler.field.r24_canonical_mul.closure` (OPEN): r24_canonical_mul / r24_guarded_qm.rs absent from frozen 4bb3b3f (P3b: eight-limb wrapping algorithm exists only in the gate)
* ClaimsUnrolledParentSource: `AspisR1ClaimsUnrolledParent.candidate_claims.claims` (OPEN): frozen 4bb3b3f has no candidate_claims.rs/module; the frozen function with this role is r1_semantic::claims (extraction attempt D05, outcome in its status)
* NJT_ClaimsRef_Funs: `NJT_ClaimsRef.r1_semantic.NJT_claims_ref` (OPEN): NJT_claims_ref is a reference function of the claims-queryscan candidate (NJT_claims_ref.rs.txt); absent from frozen 4bb3b3f; the nearest frozen function is r1_

## Reach of the 8 gate-only definitions (PCXC_NOFROZEN_REACH.json)

All 8 are reachable at constant level from AspisR1.TAS_FinalB.deployed_splitB and from at least one CLOSED-row root; none is unreachable. This is not semantic use.

* `AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value`: splitB True, 27 closed-row roots, shortest witness 9 hops
* `AspisR72Sampler.field.r23_product_u32_bounded`: splitB True, 40 closed-row roots, shortest witness 11 hops
* `AspisR72Sampler.field.r24_canonical_mul`: splitB True, 35 closed-row roots, shortest witness 10 hops
* `AspisR72Sampler.field.r24_canonical_mul.PP`: splitB True, 35 closed-row roots, shortest witness 11 hops
* `AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call`: splitB True, 35 closed-row roots, shortest witness 11 hops
* `AspisR72Sampler.field.r24_canonical_mul.closure`: splitB True, 35 closed-row roots, shortest witness 12 hops
* `AspisR1ClaimsUnrolledParent.candidate_claims.claims`: splitB True, 23 closed-row roots, shortest witness 6 hops
* `NJT_ClaimsRef.r1_semantic.NJT_claims_ref`: splitB True, 12 closed-row roots, shortest witness 9 hops

## NJT_claims_ref

NJT_ClaimsRef.r1_semantic.NJT_claims_ref is a hash-linked reference, not an orphan: the reference function (sha256 2bf403f75b4f9fb0d834bec61771d156c5555bd4fdf3dcdd804840ca58a6e5ea, NJT_REFERENCE_PINS) is appended to the frozen r1_semantic.rs (sha256 c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013) giving the scratch tree file e2a6d18185b13d5d6d7858284e30310119d53bac7e48d15c210152f847c553ea; PCWC_E002 re-extracted it byte-identically to the recorded outputs (PCWC_NJT.json). It has no counterpart in the frozen source proper because it is the reference of the claims candidate, linked to the frozen text by those hashes; it serves 12 CLOSED rows.

AspisR72Sampler.Funs was extracted from an older src/field.rs (blob a47a9996aa63, first commit 0319ac2b7b5); the frozen field.rs differs in M31::mul.
