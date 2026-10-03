# R431: actual freeze slice-iterator construction

R431 exposes the actual slice iterator constructor used by the selected freeze batch. It is audited native source evidence, not a Lean execution theorem. It does not prove pointer safety, full fold execution, privacy or soundness.

## Exact scope and receipt

The root remains `crate::freeze`. Compared with the successful R429 C command, the only changes are a fresh output destination and the two ordered includes `core::slice::_::iter` and `core::slice::iter::_::new`. All selected source, flags, features, monomorphization, offline/locked release settings, original Charon and source root remain unchanged. Launch worktree revision is `cacf6c885a3beffc89fd6be7e8f3801cd8786d2e`.

Charon exited 0, `has_errors=false`, in 14.34 seconds. GNU time reports peak RSS 630,960 KiB and zero swaps. The terminal cgroup peak is separately recorded as 492,773,376 bytes; the saved records do not explain its difference from GNU RSS. Effective limits were MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128, runtime limit 600 seconds, control-group kill and 10-second stop timeout. Terminal OOM counters are zero. Aggregate reservation checks include the existing 128 MiB website service without changing it.

Exact target: `R431ActualSliceConstruction.llbc`. Output SHA256: `df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358`. The predecessor R429 C output remains pinned at `c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465`; the R185 baseline also remains unchanged. Eight frozen source/configuration hashes, four previously pinned stdlib hashes and original tool hashes are recorded before/after. The callback source SHA256 remains `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`.

Original Charon revision is `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, with a clean tracked checkout. Wrapper SHA256 is `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`; driver SHA256 is `4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938`. Rustc remains nightly-2026-06-01, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. No translator, receiver repair, observation hook or verifier source change was applied.

Complete `#print axioms`: not applicable; this milestone runs no Lean target. The complete native graph, command, logs, resource receipts, source inventories and independent audit are retained. Large artifacts use lossless gzip with original and stored hashes; `materialize.py <fresh-directory>` reconstructs exact raw bytes for offline checks. The audit originally selected a preflight cgroup snapshot; the correction and initial report are retained. No build was repeated to correct this evidence report.

## Actual selected path

The actual selected `freeze::call` function29 calls slice `iter` function43 for its shared `QM31` slice, then passes the result to specialized fold function70. Function43 is now Transparent/Structured and moves its shared slice argument to function86, `Iter::new`, returning its result and retaining the emitted unwind path. Function86 is now Transparent/Structured at pinned `slice/iter.rs:94–104`.

The constructor reads slice metadata into local2; obtains a raw shared fat pointer from the slice reference; passes through the emitted NonNull/transmute and raw-pointer casts; branches on global31 IS_ZST; and builds iterator type42 from start pointer local3, end-or-length local5 and marker local11. The non-ZST branch computes Offset(local7, local2) into local6. The ZST branch and every storage operation remain saved. The constructor has no direct function calls in this native body.

The separate instantiated Iter::next function76 remains opaque and is not called by the actual specialized fold. It must not be substituted for that fold's counted pointer loop. Thin/fat NonNull types58/69 remain opaque declarations with captured layout records; R431 does not prove their transmute or pointer primitive semantics.

The scalar globals retain IDs31/32, but this capture renumbers their initializer functions to143/146 and the size intrinsic to154. R430 used142/145/153. Reusing that result requires explicit source-graph identification/renaming, rather than assuming function IDs are stable across captures.

Pinned source contracts are preserved beside the native rows. They distinguish nonzero pointer additions from zero-offset operations, one-past arithmetic from reads, and same-address zero-distance from same-allocation differences. In particular, legal empty slices may have a non-null aligned dangling pointer without an allocation; the proof must preserve that case.

## First remaining proposition

Connect the exact constructor and fold operations to justified pointer/metadata/transmute semantics, and prove input-slice validity, the initialized element image, pointer/end correspondence, in-bounds reads, immutable storage/lifetimes and closure power restoration. Derive the R193 load premise; do not assume it or an entire library contract. Discharge the actual source unchecked-add preconditions and preserve or justify all check/drop/unwind/failure paths. Existing R174/R184/R191 and R193/R195 results remain useful but do not prove those source premises. Vec::extend remains separate.

Whole freeze chronology and inverse Domain behavior, callback/oracle chronology through rho, universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, complete published-view simulation with shared-oracle losses, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. The 999,790 / 999,532 CU results and all security parameters remain preserved. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation was run.
