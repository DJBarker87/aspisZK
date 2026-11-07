# NMB TX1 entry spine handoff

Target not yet established. Stage 0: rules and predecessor review in progress.

Branch codex/cx-tx1-entry3-20261107. Work is confined to NMB-prefixed sources and this receipt directory. Frozen source: crates/, programs/r1-cost-probe and Cargo.lock at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465, ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Verifier ELF pins inherited, not reproduced. No shipped-file changes planned.

Order: TX1:344 stage1, 345 stage1_owned, 333 process, 330 entry, 328 first_decoded. Baseline ledger23: 580 CLOSED / 0 qualified / 19 OPEN. Only composed row closure earns credit. Budget 40 Kani / 140 Lean / 0 extraction. No launches yet.

Retained assumptions: existing runtime admissions, std/allocator and ReviewedTranscription tool trust. No new trust row. Open TX1:094 requires its exact full-strength RowSpec unless a gated root is available. NLQ source support is not a native certificate. No assumptions discharged yet.

Validation: read-only review underway; no formal result yet. Next deliverable is the stage1 transcription/cut inventory over NLF borrow tokens, per-occurrence metadata, allocator events, full child packets and SAME world chain. Each compiled theorem will carry its complete statement and standard-axioms audit.
