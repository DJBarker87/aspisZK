# NBX stub/domain ledger

No field arithmetic, SHA, syscall, successful-child, decoder or adapter-law
stub is introduced. The only actual Kani stubs are the exact prescribed KMX
copy replacements, paired with KMX_CopyMeaning and inherited NBU window laws.
Patch SHA256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
The root and crate-local KMX_stubs.rs copies are byte-equal before each run.

| Stub | Reused Lean value/frame law | Domain |
|---|---|---|
| copy_from_slice / clone_from_slice | KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame, NBU_CopyWindows.window_spec/disjoint | equal-length valid disjoint/shared Rust slices; Copy elements |
| copy_nonoverlapping | KMX_CopyMeaning.loop_spec/copy_frame, NBU_SourceWindows.array_window/live_row | valid typed Copy elements; nonoverlapping caller-provided storage |
| Vec::extend_from_slice / slice::to_vec | KMX_CopyMeaning.append_spec; exact prescribed KMX implementation | Copy elements; admitted successful allocation; no new Vec growth credit |
| alloc::realloc | KMX_CopyMeaning.realloc_prefix and inherited allocator boundary | valid old layout; preserves old allocation on failure; no new allocator credit |

Each positive whose property reaches a copy is paired with its matching
failing control; a timeout or unwinding failure would receive no credit.
No body-fidelity claim is inferred from self-composition of a decoder.
K001/K002 failed during compilation and receive no native credit.
The inherited NBU field/codec domains remain exactly those in NBU_STUBS.md;
this job does not strengthen a caller precondition to obtain a pass.
