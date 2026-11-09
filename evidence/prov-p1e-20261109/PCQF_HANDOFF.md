# PCQF_ HANDOFF: phase P1e (frozen extractions for the P2b/P2c gaps)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no equality proof written. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p1e-20261109/. Tool aeneas-b59d5188-extended (PCQF_TOOLS.json). 35 of 35 extraction scopes, 0 Lean scopes, one at a time, caps 3G/4G swap 0, 180 s unraised; peak RSS 3.0 GB (E005), others <= 0.75 GB; no kill, no timeout. Receipts PCQF_E0nn/receipt.json, PCQF_ATTEMPTS.jsonl, PCQF_RECEIPT_SUMMARY.json.

## Configuration
Every run overflow checks ON. Per the mid-task ruling (per gate module) PCQF_CONFIG_BY_MODULE.json derives ON/OFF from gate text: every function module in scope has checked arrows on + - * and no wrapping markers, so ON; type/const-only modules have no arithmetic (no effect). No OFF variant needed. Recorded in each PINS (p1e_config) and PCQF_COVERAGE.json. The classification is a regex over gate text, not proof of how the gate was extracted.

## Step 2: P transparent (PCQF_SUPERSEDES.json)
Charon `--include aspis_core::field::P` makes it `def aspis_core.field.P : Std.U32 := 2147483647#u32` (matches the gate's def form). Re-runs: PCQC_E002->PCQF_E001 (P not reached, text identical), PCQC_E003->E002, PCQC_E004->E003, PCQ_E039->E004, PCQ_E040->E005 (text identical, P not reached; the FP3-3 unparseable layout persists), PCQC_E011->E006 (also M31.ZERO, ONE, mul, reduce_u64, QM31.mul now defs, 5 items P2b listed as external-only; CM31.add/sub stay axioms). The P2c FP3-1 failures (20 definitions) can be re-compared against PCQF_E002/E003/E004 emissions. aspis-core selection of P: PCQF_E007 (def present locally).

## Fresh emissions obtained (exit 0)
E001-E007 (above, plus NEW1 aspis-core field leaf arithmetic: M31/CM31/QM31 add/sub/mul/square/mul_m31/double/ZERO/ONE/new/from_*, PreparedQm31Multiplier new/mul), E009 (state_only_prefix r0 Error/Challenges types, field types), E010 (poseidon2 consts, spend DOMAIN_*, POOL_V1_PAIR_CAPACITY, format consts), E011 (PoolV1TreeError), E013 (qm31_pack_base4), E027 (qm31_from_karatsuba_channel_sums), E030 (state_only_poseidon: extension_from_raw_limbs, extension_limbs, pow5, internal_round, interpolated_internal_pair, with internal_linear_lazy opaque). Name-level coverage in PCQF_COVERAGE.json: summary FRESH_PRESENT 59, FRESH_EXTERNAL_AXIOM_ONLY 6, NO_FROZEN_COUNTERPART 10, MISSING 178 over the 201 P2b + 52 P2c definitions (P2c count includes cut-crate and carried-failure items).

## Not obtained (PCQF_FAILURES.json has exact errors; PCQF_CLASSIFICATIONS.json PCQF-C5)
22 failed runs. Aeneas limits: qm31_sum_products3_prepared, qm31_m31_dot, state_only_poseidon (internal_linear_lazy, interpolate_three_constant_columns, external_linear_lazy, external_local_packed_raw loop), pair_forest_semantic_terminal and pair_forest_copy_terminal groups (InterpBorrows 2731 / Not_found / context match), pair_terminal validate_verified_afterstate loop. Feature finding (PCQF-C3): the audit feature set compiles out literal functions the gate has; round-2 used r0,pool-v1-kernel and Charon then accepted the roots but Aeneas failed. NO_FROZEN_COUNTERPART (not run): external_linear_lazy_row(+closure), array_from_fn_copy(+loop), trailing_zeros_aux.

## Hand models (PCQF_HAND_MODELS.json, record only): 45 external names scanned, 18 gate hand models, 27 NOT_FOUND, no trust row proposed.

## Next
The Aeneas-limited functions need a different tool (P1d is testing original Aeneas 959659a6) or hand models; the semantic/copy terminal feature configuration of the gate needs confirmation from the lead.

## Files
PCQF_extract_specs.json, PCQF_E0nn_spec.json, PCQF_E0nn_emitted/ (raw, PINS, xz logs), PCQF_COVERAGE.json, PCQF_SUPERSEDES.json, PCQF_FAILURES.json, PCQF_ATTEMPTS.jsonl, PCQF_CLASSIFICATIONS.json, PCQF_TOOLS.json, PCQF_CONFIG_BY_MODULE.json, PCQF_HAND_MODELS.json; scripts PCQF_make_specs.py, PCQF_render_spec.py, PCQF_chain.sh, PCQF_build.py, PCQF_records.py, PCQF_supersedes.py, PCQF_hand_models.py.
