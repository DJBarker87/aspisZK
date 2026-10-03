# R429: actual freeze gamma-fold source

R429 exposes the actual `QM31` slice fold used by the selected `freeze` callback. It is audited native source evidence, not a compiled Lean execution theorem. No whole-freeze, privacy or soundness claim is made.

## Scope and receipts

The requested root is `crate::freeze`. The frozen callback source SHA256 is `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`; its `K` is `QM31`. The complete R185 extract-command SHA256 is `2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96`, and its preserved LLBC baseline SHA256 is `e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31`.

The final command changes only the destination and adds four ordered includes: `core::slice::iter::_::fold`, `core::slice::iter::Iter`, `core::mem::SizedTypeProperties::IS_ZST`, and `core::mem::SizedTypeProperties::SIZE`. Existing monomorphization, source root, original Charon, flags, features, offline/locked optimized release settings and all previous includes remain unchanged. Eight source/config hashes (including the callback) and four standard-library hashes are monitored before/after.

Original Charon source revision is `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; tracked source remains clean. Original wrapper SHA256 is `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`; original driver SHA256 is `4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938`. Rustc is pinned nightly-2026-06-01, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. No observer hook, receiver repair or translator modification was used. Launch worktree revision is `956b16b46251cc24f0883a17114695ffbb960510`; the frozen verifier snapshot has no independent Git metadata, so hashes are the exact source identity.

| Attempt | Result | Wall time | Peak RSS | Swap |
| --- | --- | --- | --- | --- |
| A | preflight exit 1, before Charon | scoped service 1.260 s | GNU RSS unavailable; recorded preflight cgroup peak 397,193,216 bytes | 0 |
| B | Charon 0, GNU time 0, `has_errors=false` | 14.56 s | 630,824 KiB | 0 |
| C | Charon 0, GNU time 0, `has_errors=false` | 14.49 s | 630,092 KiB | 0 |

A detected the existing system static website service. Its complete failure is retained. Read-only inspection found a finite 128 MiB memory cap. B accounts for that cap in the aggregate reservation without raising build limits; it exposes the fold, iterator fields and IS_ZST but leaves SIZE opaque. C adds only SIZE with a fresh destination. Successful B was not rerun unchanged.

Every job used its own user systemd scope, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128, runtime limit 600 s, control-group kill and 10 s stop timeout. Actual effective limits, memory peak, swap, clean memory events, available host memory, active-unit reservations and all-user heavy-process checks are saved. The active system website cap is included in B/C reservations; it was not changed or stopped.

Final C output SHA256 is `c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465`. B output SHA256 is `3eb71115ebd990e246f79657d48c8067f52541dd406d150a76d60add7bc020af`. The independent saved-capture audit passed 58 checks, and the lead inspected the source rows and ran the focused checker. Exact plans/scripts, full logs, before/after receipts, predecessor histories and inventories are in the evidence bundle.

Large AST inventories and LLBC outputs are stored as lossless gzip. `compression-manifest.json` records both compressed and original checksums; `materialize.py <fresh-directory>` verifies the physical index and restores exact raw bytes for the saved audit scripts. Nested inventory checksum files are historical raw-byte indexes, not compressed-storage indexes.

Complete `#print axioms`: not applicable; no Lean theorem was compiled in this milestone.

## Verified source facts

The actual specialized slice fold is function 70, now Transparent/Structured, at pinned `macros.rs:259–289`. Type 42 now exposes the actual `Iter<QM31>` fields `ptr`, `end_or_len`, and `_marker`. Type 2 is `QM31` with c0/c1 and recorded x86_64 layout size 16/alignment 4. This native layout record is not a universal layout or pointer theorem.

The loop's FnMut call moves local 17. Statement 10410 creates that local by a mutable reference to closure local 3; statement 10496 calls the closure; statement 10499 ends the temporary on the normal path. The captured closure has a mutable QM31 power reference and shared QM31 gamma reference. This differs from the persistent receiver Copy in the normalization helper's default try_fold. No Copy-to-Move repair is needed at this particular actual closure-call operand, and no helper repair may be claimed to prove it.

Global 31 IS_ZST is transparent and calls structured initializer 142, which compares Global 32 SIZE with zero. In C, Global 32 and its initializer 145 are also transparent; initializer 145 calls function 153, the `size_of::<QM31>` intrinsic. The intrinsic is represented as Intrinsic with Foreign opacity. Preserve these exact identities; SIZE was opaque in B but is transparent in C. No primitive execution rule or branch elimination is proved here.

The pinned source fold returns the initial accumulator on empty input; otherwise it uses an index, loads an element through the source pointer, calls FnMut, increments with unchecked addition, and stops at the source length. All emitted checks, aborts, drops and unwind paths remain saved. These source/compiler facts do not prove their execution, safety, correspondence, or closure state restoration.

## First remaining proposition

Prove the captured actual specialized fold executes the existing counted/list-fold model, including its source-valid slice allocation and iterator construction, pointer/end correspondence, element reads and lifetimes, size/length/empty tests, closure power restoration, unchecked index operations, stopping and every legal failure/divergence path. Reuse R174/R184/R191 closure/arithmetic results and R193/R195 control/index proofs without repeating their successful unchanged checks. Those results do not discharge the missing source primitive and pointer arguments.

The earlier successful R156 whole-freeze translation still uses an opaque specialized fold. R160's expanded translation fails on a global read; R185 fails on nested-loop Option handling; R186 fails on a copied mutable borrow in a different generic Iterator fold. Preserve their histories and do not rerun them unchanged. The `Vec::extend` path is a separate obligation.

Whole freeze chronology and inverse Domain behavior, complete callback/oracle chronology, universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, full published-view simulation and explicit shared-oracle probability losses, coherent pre-beta quotient extraction and optimized-to-source acceptance remain open. The 999,790 / 999,532 CU results, all security parameters and negative/authentication/canonical checks are preserved. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation was performed.
