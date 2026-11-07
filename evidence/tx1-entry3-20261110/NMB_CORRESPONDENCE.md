# NMB source correspondence (work in progress)

Target not yet established. These are reviewed-transcription drafts, not native certificates or row roots.

Frozen `r1_pool_adapter_owned.rs:447-465` is the stage1 target. :448-450 checks both exact instruction byte strings and the account count before any SDK access; :451-455 constructs three snapshots in source order with lengths 58295/1880/1768. :456 calls stage1_owned on the exact owned array and propagates its ProgramError. :457 borrows account occurrence 2 exclusively, copies the returned checkpoint, then drops the guard; :458-459 are absent under deployed features (cu-profiling disabled); :460 returns Ok and releases owned temporaries. Allocation failure during a snapshot ends at the live shared token, without release or later snapshots.

NMB_Input.Input preserves original per-occurrence descriptors and runtime handles separately. `ofEntry` embeds the earlier cell-indexed Entry only as a specialization. `entry_snapshot` proves that specialization agrees on the complete OwnedAccount; `entry_sdk` relates all SDK state, including every payload. Neither theorem asserts that an arbitrary RuntimeEntrypointAdmission forces cell-indexed metadata.

NMB_Metadata commutes all SDK borrow/deref/release operations with metadata replacement at fixed handles; NMB_MetadataAdmission relates it to NLF's own installation. Native original-descriptor association still needs the (bg) cuts.
