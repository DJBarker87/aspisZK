# PCUI_ HANDOFF: phase P2i (equality round on the wrong-basis and failed/other records)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Branch `codex/pc-prov-p2i-20261110` (base research a64b1f4c7c6). Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace `/home/dombarker/project-offloads/codex-pc-prov-p2i-20261110/`. 29 of 60 Lean scopes (PCUI_L001-L029), 0 of 15 extraction scopes, one at a time, caps 6G/8G swap 0, 180 s unraised. Peak RSS 4.5 GiB (L028), longest wall 125 s (L029). Summary `PCUI_SCOPE_SUMMARY_ALL.json`, events `PCUI_ATTEMPTS.jsonl`, receipts `PCUI_Lnnn/receipt.json`.

## Semantic finding
None. No difference at a matching configuration that is not an encoding difference was found. Encoding difference met: the OFF emission NMH_E010 passes the shift amount at its Rust type (`wrapping_shl x 8#i32`), see PCUI-C3 (ShrAmt bridge, OFF only, 2 credited definitions depend on it).

## Claims (each in a scope whose theorem printed standard axioms only; no sorry, axiom, native_decide, raised heartbeats)
Definitions in the deployed_splitB cone that moved from OPEN to EQUALITY_PROVED: **144** (PCUI_STATUS.json, PCUI_VIEW.json; EQUALITY_PROVED 694 -> 838, OPEN 708 -> 564).
* Wrong-basis records: 101 of 119 re-proved against an eligible emission with a recorded configuration, `@fresh = @gate` by rfl against the compiled gate constant (PRVEq_<module>_i<k>.lean). 70 on an ON emission; 2 on an OFF emission whose gate declaration has wrapping_* (matching OFF); **29 on an OFF emission only with no wrapping_ in the declaration** (CONFIG_INDEPENDENT_BY_TEXT_OFF_EMISSION_ONLY): this is a lexical independence argument, not an ON emission; the lead may demote them. WRONG_BASIS open: 119 -> 18 (no identical emission: OraclePortCkptAbi2Extracted 8, NJS parametric 4, NMP 3, CircleFallback 1, RecordParser parse_record 1, NNG verify_finish 1).
* Text-only Types records: 33 of 74 proved as Equiv (generic class IND-EQUIV added to the generator: inductives by constructor-wise match; structures by the existing structure-equiv) in PRVEq_bundle_T1..T4. This is isomorphism of declarations of identical text.
* NOT_COVERED/FAILED records: 10 proved (PRVEq_bundle_O1, scope exit 1: the bundle has 43 errors; only theorems with standard axioms and no sorryAx are credited, the 47 theorems that depend on sorryAx are not). Failure classes in PCUI_OTHER_FAILURES.json.
9 modules changed rollup OPEN -> EQUALITY_PROVED in the splitB view (PCUI_VIEW.json). The 599-row count was not recomputed (PCXB kept the row reach tables in scratch).

## Assumptions
Retained: ShrAmt bridge (OFF only), externals as in the gate, the Aeneas emission text as the model of the frozen source (receipts of the emissions, not re-run). Added: none beyond PCUI-C1/C3 classifications. Supersedes: the 134+10 records listed in PCUI_ALL_STATUS.json pcui_superseded (WRONG_BASIS, TEXT_ONLY, NOT_COVERED/FAILED).

## Not established
PCUI_REMAINING.json: 18 wrong-basis without an identical emission (an extraction at ON is needed for NMP prepare/verify_observed/LOGICAL_Y1, NNG verify_finish, CircleFallback parameters), 41 type records (structures with Array/Option fields of fresh types, text differences), 34 NOT_COVERED + 34 FAILED (one failed shape each: fresh/gate carrier mismatch, unsolved goals, two heartbeat timeouts), parametric NJS/NMP gate declarations (CONDITIONAL_ON_BINDING at best). Skipped by rule: 59 cut-module records, 12 hand-model/hand-adapted, Native14, NO_FROZEN_COUNTERPART. Next deliverable: one ON extraction for the NMP/NNG start-from specs, then a second proof shape for the 34 FAILED.

## Files
PRVEq_*_i<k>.lean, _t<k>.lean, _o<k>.lean, PRVEq_bundle_T1..T4/O1 (exact concatenations, .bundle.json offsets), PCUI_STATUS.json, PCUI_ALL_STATUS.json, PCUI_VIEW.json, PCUI_REMAINING.json, PCUI_HAND_MODELS.json, PCUI_CLASSIFICATIONS.json, PCUI_TOOLS.json, PCUI_PROVED*.json, PCUI_*BASIS_CANDIDATES.json, PCUI_EMISSION_CONFIG.json, scripts PCUI_*.py/.sh, inputs/ (gate sources from research, ShrAmt prelude), gen/ (generator reports).
