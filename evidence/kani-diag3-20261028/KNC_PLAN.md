# Diagnostic plan

Frozen baseline: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Restore KNB_K008 captured source files in an isolated scratch copy, including original NBZ names and the unselected KNB module. Keep the frozen lock and resolved graph.

Stage 1: setup and provenance (no solver).
Stage 2: original-context false properties: invert only obs.is_none() to obs.is_some(); separately replace the phase payload assertion with assert!(i >= 10). Inspect each property result, not only command exit. Commit receipts and direction finding.
Stage 3: at most four name probes, preserving declaration order and logic. Rename only the module and only the selected harness function first; adapt remaining probes only if needed. Renames are diagnostic experiments, never credit repairs. Commit receipts and final finding.

Budget: at most 10 Kani commands, 2 optimized Rust runs, 0 Lean. One admitted scope at a time, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64. Admission requires allowed:true and exit 0. Existing host launcher copied unchanged; own transport wrapper only. Persistent own cache seeded by copying read-only query cache; both retained. Do not touch shared kmy cache.
