# PCQC_ HANDOFF: phase P1c (overflow-checks redo of the fresh frozen extractions)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. No equality proof written (P2/P3). Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; host workspace /home/dombarker/project-offloads/codex-pc-prov-p1c-20261109/.

## Configuration (ruling 2026-11-09)
Every run: CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true and RUSTFLAGS with ` -C overflow-checks=yes` appended to the stager flags (charon_receipt.json env_effective; PINS field extra_env_appended_to_stager_env). Specs are copies of the earlier runs' specs (PCQC_make_spec.py), changing only run id, host base, PCQ_/PCO_ -> PCQC_ and extra_env. Tools: PCQC_TOOLS.json. 25 extraction scopes of 45, 0 Lean scopes, caps 3G/4G swap 0, timeout 180 s unraised, one scope at a time.

## Redo results (usable overflow-on emissions)
S002 PCQC_E001; S005a PCQC_E002; S009 PCQC_E003; S014 PCQC_E004; S009a PCQC_E005; P0 S900 PCQC_E006; P1b S016 EbyKDot PCQC_E007; S020 E008; S017 E009; S021 E010; S015 E011; S022 E012; P0 S903 pilot PCQC_E022+E023 (PCQC_E013 timed out on the cold build; roots split). P1a PCQ_E037-E040 (S901, S001, S013, S011) were already overflow-on and are carried. PCO_E002 is superseded by PCQ_E037 (cited, not redone).
PCQC_ON_OFF_DIFF.json: generated text is identical modulo prefix for 5 of 12 compared redos (E001, E002, E004, E006, E012); it differs for 7: S009 (E003), S009a (E005), S016 (E007), S020 (E008), S017 (E009), S021 (E010), S015 (E011) (checked-arithmetic differences in Funs.lean), so the overflow-off emissions must not be used for P2 for those.

## Retry results (all ended in failure; exact errors in PCQC_FAILURES.json)
S004 order (E014), encode_digest_canonical solo (E015): Aeneas Not_found at InterpReduceCollapse.ml 1991. S010 (E016): Name clash LaneTransition. S012 (E017, E024): both killed by the 180 s timeout (Charon about 77-81 s, Aeneas unfinished); shape class retired. Dot::push (E018): InterpBorrows.ml 2731. Weights::raw (E019): nested borrows weights.rs 229. S019 (E020): InterpReduceCollapse.ml 1880. S006 and S018 not retried (brief).

## Lead addendum: compact.rs::expand_values (S1ValuesOwnedModelV1)
PCQC_E021 (no opacity) and PCQC_E025 (copy_from_slice and fill opaque) both fail in Aeneas: "Markers remain after collapsing a context", compact.rs 131:4-134:5, the zip/chunks_exact_mut loop. No fresh emission of expand_values exists; ExpandValuesFrozenEq (PCWC_S1_OBLIGATION.lean) has no fresh-extraction side from this job. The failure is in the loop itself, so further callee opacity is unlikely to help; the next shape needs a source restructure or a hand model, neither of which this job decides.

## Files
PCQC_SUPERSEDES.json (every earlier PCO_/PCQ_ E-id), PCQC_COVERAGE.json (schema of PCQ_A_COVERAGE.json plus p2_emission_dirs_per_gate_module and pilot_emissions), PCQC_FAILURES.json, PCQC_ATTEMPTS.jsonl, PCQC_CLASSIFICATIONS.json, PCQC_TOOLS.json, PCQC_HAND_MODELS.json (record only, no trust row proposed), PCQC_RECEIPT_SUMMARY.json, PCQC_ON_OFF_DIFF.json; per run PCQC_Exxx/receipt.json, PCQC_Exxx_emitted/ (PINS, raw, xz logs). Scripts: PCQC_build.py, PCQC_hand_models.py, PCQC_write_records.py, PCQC_make_spec.py, PCQC_make_variant.py, PCQC_chain*.sh.

## Run table
| run | spec | exit | wall | peak RSS |
|---|---|---|---|---|
| PCQC_E001 | S002 | 0 | 32.0 s | 0.70 GiB |
| PCQC_E002 | S005a | 0 | 82.0 s | 0.63 GiB |
| PCQC_E003 | S009 | 0 | 78.5 s | 0.63 GiB |
| PCQC_E004 | S014 | 0 | 82.3 s | 0.63 GiB |
| PCQC_E005 | S009a | 0 | 84.4 s | 0.63 GiB |
| PCQC_E006 | S900 | 0 | 32.1 s | 0.70 GiB |
| PCQC_E007 | S016 | 0 | 97.4 s | 0.52 GiB |
| PCQC_E008 | S020 | 0 | 95.6 s | 0.52 GiB |
| PCQC_E009 | S017 | 0 | 92.8 s | 0.52 GiB |
| PCQC_E010 | S021 | 0 | 95.5 s | 0.52 GiB |
| PCQC_E011 | S015 | 0 | 102.9 s | 0.52 GiB |
| PCQC_E012 | S022 | 0 | 95.1 s | 0.52 GiB |
| PCQC_E013 | S903 | 124 | 180.0 s | 0.52 GiB |
| PCQC_E014 | S004 | 2 | 31.3 s | 0.70 GiB |
| PCQC_E015 | S005b | 2 | 88.5 s | 0.64 GiB |
| PCQC_E016 | S010 | 2 | 136.0 s | 2.71 GiB |
| PCQC_E017 | S012 | 124 | 180.0 s | 0.63 GiB |
| PCQC_E018 | S016 | 2 | 94.6 s | 0.52 GiB |
| PCQC_E019 | S022 | 2 | 91.8 s | 0.52 GiB |
| PCQC_E020 | S019 | 2 | 97.6 s | 0.52 GiB |
| PCQC_E021 | S1V | 2 | 89.1 s | 0.52 GiB |
| PCQC_E022 | S903a | 0 | 98.0 s | 0.59 GiB |
| PCQC_E023 | S903b | 0 | 99.4 s | 0.64 GiB |
| PCQC_E024 | S012 | 124 | 180.0 s | 0.63 GiB |
| PCQC_E025 | S1V | 2 | 87.4 s | 0.52 GiB |

## Remaining
Unchanged gaps: S004, encode_digest_canonical, S010, S012, Dot::push, Weights::raw, S019, S1 expand_values have no fresh emission (Aeneas tool limits at b59d5188); S006/S018 outside P1. Hand-model reading: PCQC_HAND_MODELS.json has many NOT_FOUND entries because it scans every external name of each run against the module's candidate files; read per gate module.
