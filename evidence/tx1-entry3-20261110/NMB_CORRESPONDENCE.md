# NMB source correspondence (work in progress)

Target not yet established. These are reviewed-transcription drafts, not native certificates or row roots.

Frozen `r1_pool_adapter_owned.rs:447-465` is the stage1 target. :448-450 checks both exact instruction byte strings and the account count before any SDK access; :451-455 constructs three snapshots in source order with lengths 58295/1880/1768. :456 calls stage1_owned on the exact owned array and propagates its ProgramError. :457 borrows account occurrence 2 exclusively, copies the returned checkpoint, then drops the guard; :458-459 are absent under deployed features (cu-profiling disabled); :460 returns Ok and releases owned temporaries. Allocation failure during a snapshot ends at the live shared token, without release or later snapshots.

NMB_Input.Input preserves original per-occurrence descriptors and runtime handles separately. `ofEntry` embeds the earlier cell-indexed Entry only as a specialization. `entry_snapshot` proves that specialization agrees on the complete OwnedAccount; `entry_sdk` relates all SDK state, including every payload. Neither theorem asserts that an arbitrary RuntimeEntrypointAdmission forces cell-indexed metadata.

NMB_Metadata commutes all SDK borrow/deref/release operations with metadata replacement at fixed handles; NMB_MetadataAdmission relates it to NLF's own installation. Native original-descriptor association still needs the (bg) cuts.


Owned stage1, frozen owned.rs:376–419: NLD_Stage1Source is reused as the complete line-faithful emitted source. NMB_generate_typed annotates all116 NLD call occurrences with typed nominal replies and lexically live program/accounts/data/locals, keeping the source body and every branch. The manifest pins the NLD source and lists each environment. NMB_OwnedResult/NMB_TypedParentFold aim at complete Result/state/occurrence erasure, never just success. Allocator pointers/capacities and actual child footprints still require physical packet association; packed nominal values do not supply it.

Process, frozen adapter.rs process, and lib.rs process_r1_cost_probe_instruction: reuse NLQ_DispatchSource/NLQ_DispatchTx1/NLQ_EntryTx1 without duplicating their proofs. These preserve the same full child result, post-world and attempted prefixes at exact original arguments; TX1 admission is computed from the original bytes. K039/K040 cover only copied admission/dispatch fragments, so no native whole-parent realization is claimed.

First decoded, frozen lib.rs first_decoded: reuse NLQ_FirstState/FirstPacket/FirstMap source support only. The full094 child packet is unavailable. NMB_RowSpec094 only expands the older VALUE/FRAME schema; resource completeness is OPEN, and that schema is never consumed as the full ledger obligation. Error logging, native resource cleanup and exact installed digest/error slot43/44 remain explicit pending obligations.

ReviewedTranscription proposals NMB-RT-344,345,333,330,328 are SOURCE SUPPORT ONLY. No closed-row trust inventory amendment is emitted. Option-A P6/D188 tool transport and existing Std/Allocator/RuntimeEntrypointAdmission remain visible; no trust row is added or removed. NMB_HYPOTHESES.json records all retained source parameters and uninstalled physical obligations under aq2/aq5/bf2. Native certificates must prove caller clauses from actual parent states, not assume source-only success or a narrowed logging oracle.
