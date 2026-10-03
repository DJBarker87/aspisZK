# Source-capture bundle index (diagnostic only)

These archived artifacts record selected Charon LLBC extractions and a read-only Aeneas pointer-model inventory. They are retained to locate the source declarations and captured inputs considered while choosing a fixed-U64 arithmetic subcomponent. They are not Lean proofs and establish no Rust-to-Lean/source correspondence, no native-pointer adequacy, and no correctness or safety property.

## R501 raw-parts precondition capture

`r501-raw-parts-precondition/` preserves the exact launch and capture command JSON, source hashes, runner, stdout/stderr and SSH logs, result/summary receipts, LLBC output, and original checksums. Its receipt records source revision `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`, Charon exit 0, wall time 13.24 s, peak RSS 627,380 KiB, swap 0, and a 5G/7G/swap-zero systemd scope. The LLBC SHA-256 is `c46d0d1fccac80c4ece4aac9cec8143b789ede55bdae39f5f6c0aa0ad6c7f1f9`; the summary records `has_errors: false` and proof claim `None`.

The captured declaration row is DefId 21, `core::slice::raw::from_raw_parts::precondition_check`, structured and transparent. The capture summary says only one generic declaration row was recorded and no separate u8/u32 specialization row. This is an extraction index only. Exact source pins and Charon argv are in `capture-command.json`; invocation and resource limits are in `launch.json`.

## R504 alignment predicate capture

`r504-pointer-align-check/` preserves the exact launch and capture command JSON, source hashes, runner, stdout/stderr and SSH logs, result/summary receipts, LLBC output, the original `R504_FUN32_SOURCE_INDEX.md`, and original checksums. Its receipt records the same source revision, Charon exit 0, wall time 13.27 s, peak RSS 626,792 KiB, swap 0, and a 5G/7G/swap-zero systemd scope. The LLBC SHA-256 is `6265be39052b9a5897f48f9ffe5f32eb07785641255f4982e2057cdaaaefeecb`; the summary records `has_errors: false` and proof claim `None`.

The captured declaration is DefId 32, `core::ptr::const_ptr::is_aligned_to`, structured and transparent. The source-index note describes recorded LLBC operations and calls but explicitly disclaims pointer-value interpretation and source behavior. Exact pins and argv are in `capture-command.json`; invocation and resource limits are in `launch.json`.

## Native ABI and pointer-model inventory

`native-abi-pointer-inventory/` is a byte-preserving copy of the R430 read-only pinned Aeneas pointer-model and function-selection inventory, including its files and source excerpts. Its README records the library's RawPtr wrapper and `.undef` behavior, the Slice model observations, and the limited Aeneas function-selection evidence. These are source observations only, not an ABI mapping proof or adequacy result. The inventory does not prove that the capture's native pointer or `usize` corresponds to the fixed-U64 arithmetic used by R503/R506.

No Lean replay was performed for this archival task. All added files are covered recursively by the parent R503 `SHA256SUMS` manifest.
