# Current LIB handoff: F9 and complete final bundle

Target not yet established; no ledger row credit. This continuation supersedes the historical parseShape domain and module25 TX2 WAITING statements below. Current pickup: import `LIB_F9_IMPORT`.

- `LIB_ParseShapeTotal.frozen_wrong_length` proves the ACTUAL fresh frozen parse_shape emission returns Err(Parse) whenever native proof length differs from57607. `rejected` gives the exact returned error and empty event prefix. No native fact/Kani/extraction was needed; the first guard has no child calls.
- `LIB_VTx1A.parseShape` and `LIB_VLib.library.parseShape` now use domain True and the full SAME deterministic model graph on ALL Bytes. `source` preserves the original typed slice; `closed086` retains the exact former graph on its length domain; `returns`/`functional` discharge the returned-value gate (and the stronger strict graph gate). Nonrepresentable host lists use the existing raw-slice fallback; every actual typed slice roundtrips.
- `LIB_Prepared.child` and `LIB_S1.library` were rebuilt at SAME repaired VL. All six `LIB_Instances.tas136/137/087/094/328/345` rfl checks passed. R4 was rebuilt.
- `LIB_ParseShape094.empty_reference` admits Err(Parse)/[] at proof[]/k10 for every pub/env. `width_not_required` explicitly refutes the old required_width premise at this instance. The historical NNG_Nonempty094.no_candidate proof cannot be transported to it. No complete actual094 RowSpec theorem is claimed: NNG_ still owns the emitted094 observation/Ref composition and all SAME reached-child domain proofs; exact boundary in LIB_F9_HANDOFF.md.
- Module25 is now complete as `LIB_FullInstances.library`: L/D/V0/VL/P/C, with nine TX2 TAS type identities and the existing six TX1 identities. L-star and V0-star are actual LIBB_PoolLib.library/LIBB_V2Star.library; gate, Values and unchanged SAME-V0 weak registration are imported, not duplicated. No TX2 library field waits on LIBB_. Actual I.f064/EnvRep installation remains integration-owned.

F9-only details: LIB_F9_HANDOFF.md, LIB_F9_STATUS.json, LIB_F9_PROVENANCE.json. Validation, own-root audit and retained export are being finalized. No shipped source, trust item, frozen spec, key, sibling worktree or release artifact changed; no push. Original runtime/std/tool/extraction/source-to-ELF obligations remain retained.

## Historical bundle continuation (prior to F9)

# LIB bundle handoff

Target not yet established; no ledger row credited. Branch codex/cx-lib-20261107. All authorized TX1 bundle work is concrete. Earlier modules14–18 handoff is preserved in LIB_LANE_A_HANDOFF.md.

## Consumer pickup

| Module | Actual term | Exact evidence |
|---|---|---|
|22|LIB_VLib.library|All67 rev3 fields definitionally equal merged lane-A/C suppliers; LIB_VLib.<field>_exact; all20 Child fields export <field>Value and <field>_returns|
|23|LIB_Prepared.child|P-star at SAME VL; ten rfl carrier identities; full graph, Returns and original caller clauses|
|24|LIB_S1.library|C-star at SAME VL; six concrete fields; validated_public and allocation specialize SAME statement/bytes|
|25 TX1|LIB_Instances.tx1; aliases VL/P/C/D|Actual TX1 bundle; six named rfl checks tas136/137/087/094/328/345 identify exact TAS field types|
|R4|LIB_VLibR4.discharge|Actual RSL.TX1_094.R4Discharge LIB_VLib.library, specialized from canonicalScan's SAME proof slice|

Import LIB_BUNDLE_IMPORT for ledger25 NMQ_COMBINED_IMPORT plus the merged lane-A/C modules and all new bundle modules. The final additive import L201 passed; L188 is the earlier import before the new R4 module. That source change is the reason for the additive check. Missing unchanged TCK_WeakRoot0/TAS_Interfaces were copied privately byte-for-byte and compiled individually, with provenance in LIB_BUNDLE_REUSE.json. No existing supplier/spec/candidate was edited.

Module25 TX2 remains WAITING on LIBB_'s canonical V0-star, as confirmed by its committed handoff at a9552ed6529. L-star already exists as LIBB_PoolLib.library. Canonical tx2auth/Root0 registration, weak NNC_ObservedLaw.w registration for SAME V0, and TX2 TAS checks follow actual V0 delivery. No dummy V0 or duplicate modules6–13 are supplied. See LIB_REMAINING.md for member-by-member below80% budget disposition.

## What changed and what remains assumed

Discharged: VL's final assembly, P's ten type equalities, C's Public identity, concrete validated-public compatibility, and R4's specialization at actual VL. All four TX1 fallible reservation fields have Functional proofs; their values read arbitrary Env.reservation, without fixing success. Each Child retains its supplier's original domain, full Result/error/stopped arms and ordered events. Definitions never choose a native Cut or independently selected successful child.

Retained: all original same-input caller clauses/provenance; existing runtime hash/reservation, std/allocator and native-tool trust; extraction provenance and source-to-ELF obligations. P's semantic/expanded provenance must be discharged by NNG_ from its original inputs using the imported lane-C support. The Returns evaluators concern the deterministic models and do not assert native syscall totality. Type checks do not construct principal row roots. No new trust item, metric, security claim or frozen-spec change. publicDom stays the committed hd-only predicate; terminal asset canonicality remains derived on the SAME successful serialization path. LIB_CLOSED.json and LIB_CALLER_CLAUSES.json classify the hypotheses.

## Validation and retention

All111 new roots pass raw ax2 with standard axioms only; collector and #print axioms agree. Only own new roots were audited. Exact targets, source revisions/hashes, dependency/Aeneas pins, exits, wall/RSS/swap, admission and cgroup limits are retained in L182–L203 receipts and LIB_BUNDLE_VALIDATION.json / LIB_BUNDLE_TRANSCRIPT.tsv. Every scope had host free≥40GB, running-codex-scope count<6, reservation exit0 AND allowed:true, limits6G/8G/swap0/tasks64 and Lean-M7000. No timeout, OOM, raised cap or failed Lean shape. Old lane-A audits/exports remain intact.

LIB_BUNDLE_EXPORT.json identifies the copy-only retained export /home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_exports_bundle_20261111. LIB_C_IMPORTS.json pins imported lane-C objects; LIB_BUNDLE_CLOSURE_PINS.json.xz plus uncompressed SHA256 pins selected final objects, sidecars and LEAN_PATH. Caches/exports are retained; no deletions. This is a focused coherent cached check, not a cold release replay.

No shipped source changed: crates/r1/Cargo.lock remain at4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool atb936275465. LIB_BUNDLE_FROZEN_SOURCE_CHECK.json retains the comparisons and inherited ELF hashes (default f8c0ec72…, devnet63ad3e9c…, Pool e0e49c34…). No ELF rebuild trigger. No wallet/key/account/fund/authority action, sibling/session-A worktree change or push.

Final accounting is recorded after export pinning in LIB_BUNDLE_VALIDATION.json. All main modules were committed immediately after their focused compilation. Principal/ledger/release closure remains outside this delivery; the100-bit per-attempt target is not yet established.

Final:22/162 continuation scopes; resumed total110/250 including prior88. All22 exits0; total scope wall791.303s; max RSS6991532KiB; swap0. L203 pins/export passed. No remaining independent authorized TX1 member; the remaining module25 TX2 fields require externally owned actual V0-star.

Raw admission transcripts with trailing blank lines are preserved byte-for-byte as.log.xz plus uncompressed.log.sha256 (LIB_BUNDLE_RAW_ARCHIVES.json); no log bytes were normalized.
