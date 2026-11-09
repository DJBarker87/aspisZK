# PCQG_ HANDOFF: phase P1f (retry of P1e's failures with the rebuilt ORIGINAL Aeneas)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no equality proof written. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p1f-20261109/. Budget used: 18 extraction scopes of 25, 0 Lean, one at a time, caps 3G/4G swap 0, 180 s unraised, no kill, no timeout.

## Tool (PCQG_TOOLS.json)
Rebuilt original Aeneas b59d5188, sha256 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3 (P4c host workspace, read-only; asserted by the controller before each use, recorded in each PINS). Charon: original XRa_bin/charon daad69be (driver efdbe5b8). **Every PCQG_ emission is from the original Aeneas, a different tool from the b59d5188-extended behind PCQ_/PCQC_/PCQF_ emissions; P2/P3 must use the gate-compatible library for them (as for P1d).**

## Configuration
Overflow checks ON in every run (per gate module: P1e classification reused, all ON; NDE_Reference2/5 ON per PCVA_CLASSIFICATION). PCQG_CONFIG_BY_MODULE.json, PINS field p1f_config. The gate's own feature set is inferred, not recorded: audit feature set FS compiles out functions the gate contains; groups on semantic/copy terminal use r0,pool-v1-kernel (PCQF-C3), others keep P1e's feature set.

## Results (PCQG_RECEIPT_SUMMARY.json, PCQG_ATTEMPTS.jsonl, PCQG_Exxx/receipt.json)
| run | selection | exit | wall s | peak RSS GiB |
|---|---|---|---|---|
| E001 | NEW2a karatsuba_channel_sums + qm31_sum_products3_prepared | 0 | 34 | 0.70 |
| E002 | NEW2c qm31_m31_dot | 0 | 31 | 0.70 |
| E003 | NEW7 interpolate_three_constant_columns, external_local_packed_raw, packed external/full_round_packed | 0 | 82 | 0.66 |
| E004 | NEW8 external_linear_lazy + full_round group | 2 | 80 | 0.64 |
| E005 | NEW13 pair_terminal validate_verified_afterstate (+loop), encode_verified_afterstate | 0 | 84 | 0.63 |
| E006 | NEW9b semantic group A | 2 | 90 | 0.64 |
| E007 | NEW10b semantic add_* group | 0 | 94 | 0.64 |
| E008 | NEW11b semantic group C | 2 | 117 | 0.65 |
| E009 | NEW12b copy terminal group | 0 | 118 | 0.64 |
| E010 | NEW8b full_round group, external_linear_lazy opaque | 0 | 98 | 0.64 |
| E011 | semantic C, external_linear_lazy opaque | 2 | 115 | 0.66 |
| E012 | semantic A first 6 roots | 0 | 172 | 0.63 |
| E013 | semantic A last 7 roots | 2 | 141 | 0.62 |
| E014 | semantic A, empty_root opaque | 0 | 107 | 0.65 |
| E015 | semantic C, external_linear_lazy and empty_root opaque | 0 | 154 | 0.65 |
| E016 | external_linear_lazy standalone | 2 | 116 | 0.65 |
| E017 | NDE_Reference2 (reduce_ref, extension_raw_ref, ...) | 0 | 0.7 | 0.13 |
| E018 | NDE_Reference5 (link_weight_ref) | 0 | 1.0 | 0.14 |

## Obtained (name-level, PCQG_COVERAGE.json: 137 FRESH_PRESENT, 2 FRESH_EXTERNAL_AXIOM_ONLY, 42 MISSING over the 178 definitions P1e left MISSING plus the 3 NDE definitions)
All P1e failure selections except external_linear_lazy and empty_root now have a non-opaque emission: qm31_sum_products3_prepared, qm31_m31_dot, validate_verified_afterstate, external_local_packed_raw, interpolate_three_constant_columns, the pair_forest_semantic_terminal groups (A and C only with the two opaque callees below), pair_forest_copy_terminal. The original Aeneas passes the P1e failures at field.rs 1482 and state_only_poseidon.rs 238/336/440 (InterpBorrows 2731) and the copy-terminal "Not_found"/context-match failures.
NDE (E017, E018): Funs.lean and Types.lean are TEXT-IDENTICAL (diff empty) to the compiled gate NDE_Reference2 / NDE_Reference5; this resolves the P3a CONFIG_MISMATCH at text level, the Lean equality check itself (PRVEq on these modules) is P3.

## Still failing (PCQG_FAILURES.json; PCQG_CLASSIFICATIONS.json C4, C5)
external_linear_lazy: original Aeneas "Unimplemented", InterpMatchCtxs.ml:419 at state_only_poseidon.rs 156:8-172:9 (E004, E016); shape retired. empty_root: `.map(M31)` name clash "aspis_core.field.M31" (E006, E011, E013); shape retired; the extended Aeneas renames to field.M31_constructor. Both appear in the P1f emissions only as opaque axioms (FRESH_EXTERNAL_AXIOM_ONLY: counted, but they have no body). Their loops/closures stay MISSING (4 names). The semantic groups A/C and the full_round group therefore depend on those two axioms; the E004/E006/E008/E011 non-opaque emissions of the whole groups do not exist with this tool. Not retried (out of scope, P1d retired): S019, S010/S012 boxed-decoder roots. The other MISSING names are the carried P1d/P1e items.

## Not established
No emission is claimed equal to a gate definition; name-level presence is not equality. PCQG_HAND_MODELS.json is record-only obligations for external_linear_lazy and empty_root (no trust row proposed). A missing source-refinement is not a cryptographic assumption.

## Files
Per-run PCQG_Exxx/ (receipt) and PCQG_Exxx_emitted/ (PINS, raw, logs), PCQG_COVERAGE/FAILURES/ATTEMPTS/CLASSIFICATIONS/TOOLS/HAND_MODELS/CONFIG_BY_MODULE/RECEIPT_SUMMARY, PCQG_extract_specs.json, scripts PCQG_extract.py, PCQG_run.py, PCQG_run_nde.py, PCQG_nde.py, PCQG_run_host.py, PCQG_render_spec.py, PCQG_make_nde_specs.py, PCQG_chain.sh, PCQG_chain2.sh, PCQG_records.py, PCQG_build.py, PCQG_tools.py. P1F_* specs (E011-E016) were added to the spec file during the run.
