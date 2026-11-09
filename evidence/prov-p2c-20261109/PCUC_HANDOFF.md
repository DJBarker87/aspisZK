# PCUC_ HANDOFF: phase P2c (generated equality modules, statement/terminal cluster)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. Branch codex/pc-prov-p2c-20261109 (base research fd363950b73). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p2c-20261109/. Frozen source 4bb3b3f5.

## Claims (exact)
9 gate modules, 142 reached definitions (PCUC_EQ_STATUS.json totals {"PROVED_RFL": 23, "TEXT_IDENTICAL_ONLY": 14, "NO_FRESH_EMISSION": 52, "PROVED_UNFOLD": 23, "FAILED": 25, "TEXT_DIFFERS": 2, "NO_COMMON_LEAN_NAME": 3}).
PROVED_RFL / PROVED_UNFOLD (46): theorem `PRVEq.<M><tag>.<name> : @<gate ns>.PRVFresh_<M><tag>.<name> = @<gate ns>.<name>` against the compiled gate constants, compiled in the verify scopes PCUC_L004 (B1), PCUC_L005 (B2), PCUC_L006 (B3), all exit 0, `#print axioms` on all 46 only propext/Classical.choice/Quot.sound, no sorry/native_decide, maxHeartbeats only as in the Aeneas header. Fresh sources are overflow-checks-on emissions only (PCQC_E002/E003/E004/E011, PCQ_E039/E040); no CONFIG_MISMATCH (checked/wrapping) difference occurred.
Compiled-source controls (PCUC_L007/L008, PCUC-C7): TerminalDecoder.Funs 240/240, NFY_Part043 92/92, Port23PUSH_Source 8/11 (3 expected artefacts of the file-local type ArrayIntoIter). The delivered files are unchanged by the generator fix found by the control (byte-identical regeneration, PCUC-C6).

## Per module
- AspisR1TerminalDecoder.Types: {"PROVED_RFL": 4, "TEXT_IDENTICAL_ONLY": 7, "NO_FRESH_EMISSION": 3}
- AspisR1TerminalDecoder.Funs: {"PROVED_RFL": 6, "PROVED_UNFOLD": 12, "FAILED": 14, "NO_FRESH_EMISSION": 25}
- NFY_Part042: {"PROVED_RFL": 3, "TEXT_DIFFERS": 2, "TEXT_IDENTICAL_ONLY": 3, "NO_FRESH_EMISSION": 1}
- NFY_Part043: {"PROVED_RFL": 4, "PROVED_UNFOLD": 11, "FAILED": 7, "NO_FRESH_EMISSION": 3}
- Port23PUSH_Source: {"PROVED_RFL": 4, "FAILED": 4, "TEXT_IDENTICAL_ONLY": 1, "NO_COMMON_LEAN_NAME": 3}
- AspisR1PublicPreparation.Types: {"PROVED_RFL": 1, "NO_FRESH_EMISSION": 12, "TEXT_IDENTICAL_ONLY": 3}
- AspisR1PublicPreparation.Funs: {"NO_FRESH_EMISSION": 1}
- AspisR1AdapterReconstruct.Types: {"PROVED_RFL": 1, "NO_FRESH_EMISSION": 3}
- AspisR1AdapterReconstruct.Funs: {"NO_FRESH_EMISSION": 4}

## What failed or is open (data for P3, PCUC_FOR_P3.json groups FP3-1..4, PCUC_CLASSIFICATIONS.json)
- FP3-1 EXTERNAL_CONST_FORM (20 definitions of TerminalDecoder.Funs/NFY_Part043): gate `def aspis_core.field.P : U32` vs fresh `axiom aspis_core.field.P : Result U32`; digest_is_canonical, validate_common, decode_common and every caller fail to type-check against the gate.
- FP3-2 LOOP_RETURN_ENCODING: pair_forest_accounts digest_is_canonical(_loop,_loop.body), output_lane: gate loop returns Bool, fresh Option Bool plus pending_return (a different loop translation, not numeric).
- FP3-3 FRESH_PARSE_ERROR: decode_pool_v1_pair_verified_afterstate_v1 (PCQ_E040) is not valid Lean as emitted (all tokens of a match arm at one column); original file inspected.
- FP3-4 Port23PUSH_Source: hand-adapted gate (field.M31 names, explicit iterator parameter); update_residue_row_loop0/update_residue_row/BatchedWeights.push not comparable.
- NO_FRESH_EMISSION (52): S005 encode_digest_canonical, S010, S012 (timeouts), S011 gaps, S007/S008 never run, and the cut crates AspisR1PublicPreparation.Funs/Types (13), AspisR1AdapterReconstruct (7). AdapterReconstruct.Funs was checked first: the gate candidate is byte-identical to the archived original Aeneas output in adapter-reconstruct-432-20261016/source-extraction-proofs.tar.gz (gen/adapter_archive_check.json), an archive-linked emission and not a fresh overflow-checks-on one (PCUC-C8).
- TEXT_IDENTICAL_ONLY (14) inductives/structures: not proofs. Hand models (record only, no trust row): PCUC_HAND_MODELS.json (43 entries, 15 where the gate defines a name the fresh emission keeps opaque).

## What ran
8 of 40 Lean scopes, 0 extraction, one at a time, caps 6G/8G swap 0, 180 s, unraised; no kill/timeout. L001-L003 probe (exit 1 expected), L004-L006 verify (0), L007 control (1, generator defect found), L008 control (1, Port23 artefact). Receipts PCUC_L00n/receipt.json and PCUC_ATTEMPTS.jsonl; wall 3.8-27.5 s, peak RSS up to 5.87 GB.

## Files
PRVEq_*.lean (final per label; PRVEq_bundle_B12/B22/B32 are the verified compile vehicles, B11/B21/B31 the probes, C11/C12 controls), PCUC_EQ_STATUS.json, PCUC_FOR_P3.json, PCUC_HAND_MODELS.json, PCUC_CLASSIFICATIONS.json, PCUC_TOOLS.json, PCUC_ATTEMPTS.jsonl, gen/ (states, reports, logs), inputs/ (fresh and gate sources used), tools and scripts.

## Remaining
P1 re-extraction with aspis_core::field::P transparent (or a P3 transport lemma); the loop-encoding refinement; re-layout question for the unparseable fresh declaration; S005/S010/S012 emissions; Aeneas generator Equivs for the 14 text-identical type declarations; cut-crate PublicPreparation and AdapterReconstruct emissions.
