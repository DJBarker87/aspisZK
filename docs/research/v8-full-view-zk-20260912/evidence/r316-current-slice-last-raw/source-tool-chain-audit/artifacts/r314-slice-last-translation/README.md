# R314 focused Slice.last translation

R314 translated the unchanged R309 three-row LLBC projection with the locally built R312 Aeneas binary. Translation exited 0 under a `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128` systemd scope. No Lean compilation or template completion was run.

The selected input root is stable LLBC `Fun def_id 12` (input Rust pattern `core::slice::{Impl}::last`). Aeneas' emitted manifest normalizes the generic Rust pattern to `core::slice::{[T]}::last`; it emits exactly one function entry for `def_id: 12`, whose manifest `lean_name` is `AspisR314SliceLast.core.slice.Slice.last`. The audit derives the declaration suffix from that manifest name and finds the actual definition at line 23 in `generated/AspisR314SliceLast/Funs.lean`. The translator emitted no warnings. It emitted no external template files, so no axiom-hole result is claimed.

Launch revision: `b268da1cb6878d9b1ab6c2cab79b0592d04dd0ca`. Input LLBC SHA-256: `9264aea58bf430b023ed8124bf8737ef6943e97230f08aa7982648f4f7557421`. R312 binary SHA-256: `fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f`. Full command, host reservation, logs, generated manifest and source payload hashes are recorded alongside this file. The root matcher correction was performed as a post-translation audit only; the translation was not rerun.
