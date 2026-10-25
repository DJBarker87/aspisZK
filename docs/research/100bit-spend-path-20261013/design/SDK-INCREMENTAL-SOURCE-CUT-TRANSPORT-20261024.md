# Incremental SDK source-cut and S1 trace transport release

> Comparison qualification (2026-10-25): historical sameDeclaration / Expr-BEq comparisons below ignore binder names and annotations. “Strict”, “identical” and “same type” based only on that helper mean full recorded metadata plus alpha expression equality, not binder-sensitive literal equality. See [SDK-EXPR-COMPARISON-QUALIFICATION-20261025.md](SDK-EXPR-COMPARISON-QUALIFICATION-20261025.md). Raw terms/hashes, exact source copies and ordinary kernel-checked results are separate preserved evidence. Historical receipts/releases are unchanged.

Status: requested CURRENT-side incremental raw data is released; original/current kernel reconstruction and enclosing source/security closure remain OPEN. No production, protocol, verifier or artifact change. No host compiler/solver; no lead reserved attempt used.

## Released input for the enclosing owner

`/private/tmp/s126-sdk-current-incremental-release-20261024-v1`

Manifest SHA256: `49c56b6cfa3ace9d747c9616bfbaea48c39823089adb2eb0bfaacc7cec1e0e83`.

Reuse the exact existing immutable base `/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1`, manifest `e55b656c8c5abb11c769f4a5c6b5e5ab574e061b437a26240c2c65c25c542226`. The new release contains ONLY 141 new raw module transports, 1,219 new constants and 34138800 raw bytes. The 1,287 baseline payloads were hash-checked and reused; none was reserialized or replaced. 53 incremental fragments extend existing module labels; there are 1375 distinct module labels across 1,428 raw transports. Read both fragments and merge by full constant name with strict comparison; NEVER overwrite a baseline module path with its incremental fragment. These files are not trusted-importable replacement modules. All files are read-only, directories mode0555. No live cache access is authorized by this release.

The request is the final section of HANDOFF-SESSION-A-20261021.md at immutable06d6684215. Seeds include complete FirstCut/SecondCut/SourceCuts/Public and the requested bytes_injective/same_inputs/source_cut_reuse, accepted_sdk_all_cuts, sdk_stage1_source_cut_numeric, originalFirst/first_eq_original and both original_sdk_* consumers. The new checked original SDK preparation/claim/trace/challenge-range theorem from58502da1a8 is an additional seed, preserving its explicit standing premises. Full type/opaque proof value, mutual inductive/constructor/recursor/rule RHS closure uses original compiled names, binders and levels. Original reflected body/helper inputs remain pinned by the earlier enclosing-cut packet; that source and its compiled terms are not reconstructed by informal renaming.

Combined read-only data audit: 1,428 modules,28,506 unique constants,43 strictly identical duplicates,0 conflicts,0 unresolved constants and0 missing seeds. The one raw unsafe/partial compiler auxiliary is the SAME base reserve._unsafe_rec; no new unsafe declaration was introduced. It remains raw data only, not a logical proof seed; consumer unsafe/partial rejection must not be weakened. Imports/extraConstNames/extension entries are empty in every raw module. NO ModuleData is inserted into a trusted environment by these tools. Data closure is not kernel reconstruction or source/native/security correspondence.

## Fresh proof dependency, explicit and local

The initial incremental export failed with the same two historical generated match_2 names encountered earlier, now referenced by AdapterRwAccepted.first_call. Its cached object SHA38328c173f4c1f6d91cc96e08e5862619e7ff214b6045180f53ba977ab6f4688 was not silently certified. We replayed BYTE-IDENTICAL published97caa13d92 AdapterRwAccepted.lean source against the selected current Model/Cuts. Both first_call and first_proof_shapes passed and were audited with standard axioms only. Fresh object SHA2af7274977c5602baafeb1c32d24684fc2955b8e047bd277f3b8922e486fa7eb.

The read-only comparator verified both complete old/new theorem TYPES strictly identical. Source, hypotheses, computational model and conclusion did not change; proof dependencies were refreshed. All other selected input content hashes matched the pre-refresh preparation. No constant from AdapterRwAccepted was in the baseline transport, so this is an explicit selection for NEW data, not a replacement of baseline raw terms. The old EntryPrivileges same-statement refresh is inherited from the base and remains separately identified. Historical compiler/import receipts are not rewritten as if produced with the new proof object. The shared enclosing proof must review/select these fresh logical declarations, then kernel-replay; no old mixed-cache coherence is claimed.

The inherited input-pins-v2 base_inputs_checked_unchanged flag records the ORIGINAL v1 preparation check. It is not an assertion that the freshly selected AdapterRwAccepted object retained its old hash; changes lists that one difference and proof-refresh-qualification.json makes the scope explicit. Full selected input postchecks after export and audit passed. The exact failed initial export remains in the ledger, including its incomplete raw staging directory, and is excluded from release.

## Validation and operational history

Fresh local jobs used the atomic lock, -j1 -M4400 and warm caches:

| Target/attempt | Exit | Wall seconds | RSS bytes | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| AdapterRwAccepted / sdk-current-accepted-proof-replay-v1 | 0 | 10.863992417231202 | 2329362432 | 0 | two standard-only reports |
| S126SdkIncrementalExportV1 / sdk-current-incremental-export-v2 | 0 | 15.759058292023838 | 1355776000 | 0 | N/A: IO raw data |
| S126SdkIncrementalAuditV1 / sdk-current-incremental-audit-v1 | 0 | 90.3804149995558 | 1662812160 | 0 | N/A: IO raw data |

Failed original incremental export: exit1,19.77376570785418s,RSS1369096192B,swap0; same two missing historical PROJECT helpers, no memory pressure or cap rise. Exact commands, source revision/content/tool/import/object pins and logs are retained. No unchanged full proof replay was performed.

An earlier prepared duplicate full export was interrupted while WAITING for an empty unknown local lock, before any compiler launch, after discovering the lead's incremental-only request. Its preflight records not_launched. The incremental runner also initially waited. The lock subsequently disappeared externally; we never removed the unknown lock. The user's asynchronous ownership/cleanup question became unnecessary; no authorization was inferred from elapsed time. Ordinary known own-runner locks were acquired/released thereafter.

Source-only focused-extractor-proof-packet-v1 evidence: evidence/s126-current-caller-20261021/sdk-current-incremental-20261024 and per-attempt receipts. No binaries or large derived logs are distributed in Git; raw transports/full logs live only in the immutable release. Metadata checks passed:

```
python3 tools/s126-sdk-incremental-20261024/check.py
python3 tools/s126-sdk-incremental-20261024/check.py --released
```

## Exact remaining obligations

This discharges the requested incremental CURRENT-data acquisition prerequisite and removes the stale Accepted proof's missing project references from the selected raw closure. It does NOT close a new whole S1/S6 soundness theorem. Original/current coherent kernel declaration reconstruction/comparison with ALL14, actual child/event/mark installation and final artifact/source/release re-pin remain lead-owned. No agreement with ORIGINAL data is inferred from this CURRENT-only audit.

S1 still needs native prepared_claim and Claims allocation/initializedness/drop/full-loop association; concrete Terminal and remaining mask/terminal reached domains; native arithmetic/Std/abort/effect transport. Returned eta/challenge ranges are now discharged at the accepted SDK caller by58502da1a8. The same-source Prepared.new, same gamma scratch/borrowed claim and joint S2 trace results remain accepted-call theorems with explicit partial Ops/B and trace interpretation boundaries. They do not supply an adaptive oracle probability law.

A separate pinned upstream Kani API assessment rejects mem-predicates WITHOUT uninit-checks as an initializedness proof route (S1-INIT-API-ASSESSMENT-20261024.md). It is source inspection, not a new native proof or permission for an unchanged failed Kani rerun. New heavy work still needs fresh reviewed admission. S2 remains transferred. The original <=2^-100 per-attempt target is NOT YET ESTABLISHED.
