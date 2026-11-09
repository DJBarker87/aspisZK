# PCQ_A HANDOFF: phase P1a (fresh frozen extractions, aspis-core and aspis-statement)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed. Equality proofs are P2 and were not written.

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (tree d461fbc56cec8ba29678d6613fc38e6c795d6a66). 40 of 40 extraction scopes used (PCQ_E001..E040), 0 Lean scopes. Caps 3G/4G, swap 0, timeout 180 s, no kill, no cap raised. Wall 22-110 s, peak RSS 0.5-3.0 GB (receipts, PCQ_A_ATTEMPTS.jsonl).

## 1. Overflow-checks finding (lead, binding)
PCQ_A_OVERFLOW_DIAGNOSTIC.json: with CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true and RUSTFLAGS "-C overflow-checks=yes" (appended to the stager's thread-limit flags, which cannot be edited), PCQ_E037 emits M31.neg as `field.P - self`, equal to NFG_CheckedFieldRef.Funs; PCO_E002 (off) emits `wrapping_sub`. CM31.neg and QM31.neg are identical in both. PCQ_E037-E040 use it, recorded in PINS (extra_env_appended_to_stager_env) and the spec.

Runs made WITHOUT it (to be superseded; nothing deleted): successes PCQ_E001, E002, E004 (empty-Funs shape), E007 (empty-Funs shape), E014, E018, E026, E030, E032, E036; all failed attempts E003, E005, E006, E008-E013, E015-E017, E019-E025, E027-E029, E031, E033-E035. Redone with it: S901 (E037), S001 (E038), S013 (E039), S011 (E040, collected read-only after an ssh drop, not resubmitted). Still to redo with it: S002, S005a, S009, S014 (E002, E014, E026, E036), and every failed selection (none was retried with overflow-checks on; failures are Aeneas interpreter errors, not shown to depend on it).

## 2. Per-spec result (PCQ_A_COVERAGE.json; name-level presence only, not equality)
| spec | status | evidence |
|---|---|---|
| S001 field | covered 3/3 | E038 (on), E001 (off) |
| S002 r0::heap | covered 1/1 | E002 (off) |
| S003 r0::Error (types-only) | covered | r0.Error in E002/E001/E037/E038 |
| S004 r0::transport::order | FAILED | E003, E006 |
| S005 atomic_statement | partial 6/9 | decode, unwrap, AtomicStatementError via E014 (off); encode_digest_canonical (+loop, loop.body) FAILED (E015, E025), left opaque elsewhere |
| S006 asq8_payment_reference | FAILED | module is cfg(test/kani/aeneas_ref), not in the frozen build |
| S007, S008 (types-only) | covered | constants and PoolV1TreeError appear in E039/E040 and others |
| S009 pair_forest_accounts | covered 5/5 | E026 (off); first_canonical_byte calls the opaque encode_digest_canonical |
| S010 pair_forest_terminal | FAILED 0/12 | Aeneas name clash, then opaque-enum crash |
| S011 pair_terminal | partial 4+1/7 | E040 (on), E032 (off); validate_verified_afterstate (+loop) and encode_pool_v1_pair_verified_afterstate_v1 opaque, MISSING |
| S012 pair_tree_profile | FAILED 0/13 | validate_... Unreachable (solo E024), name clash |
| S013 payment_relation | covered 48/48 | E039 (on), E030 (off) |
| S014 spend::VALUE_LIMIT (types-only) | covered | E036 (off), root encode_atomic_payment_statement_v4 |
Exact error texts: PCQ_A_FAILURES.json. Classifications and every selection change: PCQ_A_CLASSIFICATIONS.json and each spec's p1a_note.

## 3. Gate modules ready for the P2 generator
Emission dirs are PCQ_Ennn_emitted/raw/<namespace>/ . Prefer the overflow-on runs.
- NFG_CheckedFieldRef.Funs/.Types, and field defs of RPz7_FIo_NativeFuns: PCQ_E038 (PCQ_PCQ_aspis_core_field); is_zero chain and field.P: PCQ_E037.
- RPz7_FIo_NativeFuns r0.heap.filled / r0.Error: PCQ_E002 (off; redo).
- AspisR1TerminalDecoder.Funs/.Types, NFY_Part042/043, AspisR20Request defs for payment_relation: PCQ_E039; pair_terminal (partial): PCQ_E040; pair_forest_accounts: PCQ_E026 (off); atomic_statement decode/unwrap: PCQ_E014 (off); VALUE_LIMIT: PCQ_E036 (off).
- NOT ready: order, encode_digest_canonical, asq8 reference, pair_forest_terminal, pair_tree_profile.
Equalities that call an opaque encode_digest_canonical are conditional on a proof of that function (axiom in the fresh emission, body in the gate).

## 4. Hand models (PCQ_A_HAND_MODELS.json, record only)
38 entries across covered modules; 19 have a gate-side concrete definition (def/abbrev), e.g. core.result.Result.map_err, alloc.vec.Vec.try_reserve_exact, alloc.collections.TryReserveError (gate: P6/NP6 StdModel), aspis_core.field.M31.from_le_bytes/to_le_bytes (a gate def, an axiom in the fresh emission because aspis_core is a separate crate); 9 entries are externals only because this job made them opaque (tagged). Slice.Insts.CoreCmpPartialEqArray.eq has no gate declaration in the searched files. No trust rows added or proposed.

## 5. Remaining
Rerun S002, S005a, S009, S014 with overflow-checks; retry failed selections with the same flag if scopes are granted; resolve encode_digest_canonical and the pair_tree_profile / pair_forest_terminal Aeneas failures (tool or source-shape question, not decided here); gate feature set of the historical statement extraction is unrecorded (A1).
