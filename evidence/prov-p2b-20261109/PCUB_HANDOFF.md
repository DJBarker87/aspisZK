# PCUB_ HANDOFF: phase P2b (generated equality modules, RPu_FIq_* / RPv_* cluster)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. Branch `codex/pc-prov-p2b-20261109` (base research fd363950b73). Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace `/home/dombarker/project-offloads/codex-pc-prov-p2b-20261109/`. 4 of 40 Lean scopes, 0 extraction scopes, strictly one at a time, caps 6G/8G, swap 0, no kill, no timeout, no cap raised.

## 1. Claims established (against compiled gate constants; PCUB_EQ_STATUS.json is the per-definition list)

Cluster: 17 RPu_ modules and 9 RPv_ modules from PCO_PARTITION.json, 222 reached definitions (PCUB_PARTITION.json). Result per definition: PROVED_UNFOLD 6, PROVED_RFL 1, PROVED_EQUIV 7, TEXT_IDENTICAL_ONLY 1, FRESH_EXTERNAL_AXIOM_ONLY 5, NO_COMMON_LEAN_NAME 1, NO_FRESH_EMISSION 201.

Proved (verify scope PCUB_L004, exit 0, 92 `#print axioms` lines, only propext / Classical.choice / Quot.sound, no sorry, no native_decide, maxHeartbeats only the Aeneas header value 1000000 copied from fresh emissions):
- RPu_FIq_Native01: `field.P`, `field.M31.add`, `field.M31.sub`, `field.M31.double`, `field.mul_by_r` equal the aspis-core fresh emission PCQ_E038 (overflow-checks on). The fresh and gate bodies are text-identical with identical Source line ranges; no checked/wrapping difference.
- RPu_FIq_Native11: `pool_v1.format.POOL_V1_TREE_DEPTH` equals PCQ_E039.
- RPu_FIq_NativeTypes: `field.M31` (rfl), `field.CM31`, `field.QM31` (Equiv, PCQ_E037), and Equivs for PoolV1WithdrawalPublicV1, PoolV1PrivateTransferPublicV1 (PCQ_E039, PCQC_E023), PoolV1PairVerifiedAfterstateV1 (PCQ_E040, PCQC_E023), PoolV1PairLiveSnapshotV1, PoolV1PairLatePublicStatementV1 (PCQC_E023). These need the recorded `--rename-fresh` rewrites (aspis_core.field.M31 -> field.M31; aspis_statement. -> ''), which change names only, not gate constants (PCUB-C5). An Equiv is an isomorphism of structures, not a type equality.
- These statements say the fresh frozen aspis-core / aspis-statement declaration equals the gate constant. The gate names the crate aspis_r1_mask_extraction_probe, which is not in the frozen tree; nothing here shows the probe crate equals the frozen crate for any item outside the 14 compared (PCUB-C3).

Self-copy controls (candidate text as the "fresh" emission): NativeTypes 30 of 30, Native11 8 of 8, Native01 34 of 38. The 4 failures are whnf heartbeat timeouts at the default limit on text-identical sides (PCUB-C4), listed in PCUB_FOR_P3.json as CONTROL_FAILURE; not rerun with a raised limit.

## 2. What is not established

- 201 reached definitions have no usable fresh frozen emission (NO_FRESH_EMISSION): Native02-10, 13, 14, CopyPrefix, External, most of Native01/NativeTypes, and all RPv_ slices. They keep their rows conditional. Provenance: the modules are transformed copies of retained mask-probe emissions or declaration slices (PCUB_PROVENANCE.json: 17 of 26 modules have declarations byte-equal to the retained R-group parent RPz4_SelectedMaskFuns only for Native01 (19) and Native02 (7); the RPv headers claim byte copies of a "G" that was not located by name). Spec routing: PCO_extract_specs.json cut C001 / C005 (route P4), PCWB_CUT_TRIAGE.json "nothing". 182 of the 201 Rust items exist in the frozen tree by name; `external_linear_lazy_row` and `array_from_fn_copy` do not (probe-only helpers). PCUB_FOR_P3.json lists them per frozen file as NEEDS_FRESH_EMISSION. No extraction was run (budget 0).
- 5 definitions (M31.ZERO/ONE/mul/reduce_u64, QM31.mul) have only an opaque External axiom in the fresh cost-probe emission PCQC_E011: no equality possible.
- r0.Public (NativeTypes) is TEXT_IDENTICAL_ONLY (no Equiv shape), `field.M31_constructor` has no same-named fresh declaration.
- Hand models (PCUB_HAND_MODELS.json, record only, 34 entries): RPu_FIq_NativeExternal (21 hand-written core/std models: U16 count_ones/trailing_zeros, Array/Option/Result/iterator folds), NativeTypes (`core.array.iter.IntoIter := List T`, 5 `read_discriminant` helpers), Native13 COPY_PATTERNS, PreparedSum3 closure, and the 5 Aeneas-translated gate definitions above. No compared theorem depends on one.
- No SEMANTIC or CONFIG_MISMATCH difference arose (all compared bodies identical).

## 3. Scopes (PCUB_ATTEMPTS.jsonl, PCUB_L00n/receipt.json, admission JSON per scope: host < 6, Stream C < 3, disk >= 40 GB)

| scope | target | exit | wall s | peak RSS KiB |
|---|---|---|---|---|
| PCUB_L001 | bundle P1: probes Native01, Native11, NativeTypes_a and three controls | 1 (expected: 4 control timeouts) | 60.4 | 2745108 |
| PCUB_L002 | bundle P2: probes NativeTypes_b, _c, _e | 0 | 2.6 | 2645896 |
| PCUB_L003 | bundle P3: probe NativeTypes_ctl (after generator change 4) | 0 | 3.1 | 2694556 |
| PCUB_L004 | bundle V1: final verify of all nine files | 0 | 4.9 | 2796328 |

Source revision at launch fd363950b7 with the new evidence directory untracked (dirty flag in receipts). Probe receipts contain sorryAx lines from error recovery; they are not deliverables.

## 4. Files

PRVEq_RPu_FIq_Native01.lean, PRVEq_RPu_FIq_Native11.lean, PRVEq_RPu_FIq_NativeTypes_{a,b,c,e}.lean (finals), `*_ctl.lean` (controls), PRVEq_bundle_{P1,P2,P3,V1}.lean (compile vehicles), PCUB_EQ_STATUS.json, PCUB_FOR_P3.json, PCUB_HAND_MODELS.json, PCUB_PROVENANCE.json, PCUB_CLASSIFICATIONS.json, PCUB_TOOLS.json, PCUB_ATTEMPTS.jsonl, gen/ (states, reports, probe logs), inputs/ (gate sources with inputs/gate_sources.json, fresh copies, parent). Reproduce: `bash gen_controls.sh; bash gen_types.sh`, generator command lines in jobs.tsv, `bash ingest.sh <bundle> 1 2 <log>`, `python3 -B PCUB_final.py; python3 -B PCUB_hand_models.py`.

## 5. Next

(1) P4 / a frozen spec for the aspis-core field.rs items (CM31/QM31 arithmetic, qm31_sum_products3_prepared, pack_base4, M31.mul/reduce_u64 which need non-opaque emission) and the aspis-statement state_only_poseidon / pair_forest_semantic_terminal / pair_forest_copy_terminal items listed in PCUB_FOR_P3.json; then rerun this pipeline (jobs.tsv: add rows). (2) Decide how the RPv slices' unlocated parent "G" is to be tied to a fresh emission. (3) The probe-only helpers (external_linear_lazy_row, array_from_fn_copy) have no frozen counterpart at all: a source-level question for the lead.
