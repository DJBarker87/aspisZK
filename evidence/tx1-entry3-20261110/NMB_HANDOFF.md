# NMB TX1 entry spine handoff

Target not yet established. Stage 0: rules and predecessor review in progress.

Branch codex/cx-tx1-entry3-20261107. Work is confined to NMB-prefixed sources and this receipt directory. Frozen source: crates/, programs/r1-cost-probe and Cargo.lock at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465, ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Verifier ELF pins inherited, not reproduced. No shipped-file changes planned.

Order: TX1:344 stage1, 345 stage1_owned, 333 process, 330 entry, 328 first_decoded. Baseline ledger23: 580 CLOSED / 0 qualified / 19 OPEN. Only composed row closure earns credit. Budget 40 Kani / 140 Lean / 0 extraction. No launches yet.

Retained assumptions: existing runtime admissions, std/allocator and ReviewedTranscription tool trust. No new trust row. Open TX1:094 requires its exact full-strength RowSpec unless a gated root is available. NLQ source support is not a native certificate. No assumptions discharged yet.

Validation: read-only review underway; no formal result yet. Next deliverable is the stage1 transcription/cut inventory over NLF borrow tokens, per-occurrence metadata, allocator events, full child packets and SAME world chain. Each compiled theorem will carry its complete statement and standard-axioms audit.

## Stage 1 in progress

Validated: NMB_Metadata, MetadataBorrow, MetadataScalar, MetadataAdmission, Input, MetadataCopy, Snapshot, SnapshotAcquire, SnapshotReturn, SnapshotPrefix, InputSnapshot and SnapshotSkip (each current-source receipt in NMB_ATTEMPTS). The metadata carrier is by account occurrence, and all fixed-handle SDK operations and full copy outcomes commute with its replacement. The earlier cell-indexed Entry is proved a specialization only. Normal snapshots restore the SDK world; malformed extents skip allocation; allocator fail/div prefixes retain the live shared token. These are source/SDK support, not full native parent folds.

K001 whole actual-stage1 child-boundary contract timed out externally at180s after optimized compilation; K002 isolated ONE full arbitrary58295-byte vector/array-move window also timed out in CBMC at90s. Both earn no credit; neither shape may be rerun unchanged. Frozen graph checks pass, and both post-run/recovered lock hashes remain frozen. No matched negative control exists. The native callbacks overapproximate entire snapshot payloads and the owned-child Err arm; this replaces zero-fill restrictions but does not by itself prove full call-argument correspondence.

Pending drafts: per-occurrence CLOSED343 value specialization and one original SDK world chain; complete source stage1 suffix/fold and own-input copy-domain discharges. No new row root or candidate is emitted. Full allocator identities, native parent cuts, and owned-child full packets still need composition. No source/ELF/security assumption is discharged, retained trust unchanged, and no new trust item is used.
