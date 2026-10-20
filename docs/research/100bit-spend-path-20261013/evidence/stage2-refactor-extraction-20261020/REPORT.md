# Stage-2 refactor and extraction (2026-10-20)

VERIFIER SOURCE CHANGE, authorized by LEAD-DECISION-STAGE2-REFACTOR-20261020.
Stage 1 refactor runtime gates PASS (`7d4c136f0`). Stage 2 pinned Aeneas extraction FAILED. Stopped as instructed; stage 3 not attempted.

## Source change

Apply the retained finish candidate: scalar fold guard, explicit one/two rounds, indexed final dot. Replace resume’s mutable Reader capture in from_fn with an indexed 22-element read, in the same order. Move the accumulator fields out before finishing the pending weights and reconstruct it before the final relation call; no allocation or arithmetic is added. Compact and multiproof source require no edits at this point.

## Execution policy

Dedicated host workspace: /home/dombarker/project-offloads/codex-cx-stage2b-20261020. Reuse a private copy of the adoption caches and harness. Each run uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, optimized Rust, -j4 and RUSTFLAGS=-C link-arg=-Wl,--threads=4. Initial observed reservation: three other 8 GiB scopes (24 GiB); adding one stays below 55 GiB. Host global swap usage is pre-existing; task scopes prohibit swap.

## Remaining obligations

Refactor runtime gates and the rebuilt verifier pin are complete. Full-cone Aeneas extraction failed; all three first facts remain obligations. R13/R12 source/model/Checks refinement, R15 checkpoint provenance/canonicality, R19 all-input oracle bound and S8 re-pin remain open. No soundness claim.

## Refactor gate results

- Codec: 1,233 outputs byte-identical, SHA-256 `3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321`.
- Ordered audit trace: 583 calls, counts and acceptance equal the adoption baseline (which checked D70). Adopted compact verifier trace: 1,095 calls, counts and acceptance equal adoption. Only unordered repeated-input summaries are sorted.
- Program/checkpoint suite: 33 passed, including all 23 checkpoint cases. Default crate: 16 unit and 14 integration tests. Detail/optimized-terminal: 16 passed.
- Pool: default 87, R1/source-invariant 118, all features 123, v7 candidate 123; each also passes 2 integration tests.
- Proof-size teeth: pass. Strict/authenticated tx2: 9,253 trace entries identical; proof/public/checkpoint mutations rejected.
- SBF rebuild and strict complete-linked-ELF stack audit: pass. Stripped ELF SHA-256 `0622ad3f19b81d71776f1a0b2fdb624cca3f371c7c4bccb14adc8ea1dfbc8090`, 1,403,912 bytes; linked ELF `3d31ff96d1257f31bd6ccb5a535610f6665ac0307cf09452b3940c03b0f5513f`, 1,459,344 bytes. No binary committed.
- Six-fixture CU: all accepted and all meet stage 1 ≤ B1, settlement ≤ B1 + 10,000; see `cu.json`. Settlement deltas: transfer 13 +7,389; 255 +7,123; 1023 +6,960; withdrawal 13 +8,492; 255 +6,877; 1023 +4,715. Saved adoption proofs are replayed through the **new SBF ELF** using the retained adoption driver and unchanged B1 Pool/registry. Driver-native checks refer to its old native dependency; fresh native checks are independently supplied by this packet's gates.
- P_R1 retry gate: **8/8 accepted and verified**, separate retry loop accepted in 1 attempt and verified. Optimized refactored native verifier (strict tx1+tx2 and dense). Exit 0; wall 458.761 s; peak RSS 582,900 KiB; zero swaps. All task receipts report zero swaps.

## Input staging and harness failures

No failed test result has been suppressed. Initial commands failed before testing because the reduced host source copy omitted `c3/build`, the generated writer glue, checkpoint include_bytes fixtures, and the historical eight-way teeth fixture. Each omission was corrected before a new uniquely named run. A harness-only preflight had an invalid dictionary key while adding the TasksMax receipt field; it launched no test and was fixed. Failed compiler receipts are retained; `receipts/harness-preflight-key-error/preflight.json` records the untimed preflight error (the original empty directory remains on the host). These are environment-input changes, not unchanged regression reruns.

The scope wrapper records command, exit, wall, RSS, swap, cgroup caps and flags for each run. `pins/build-inputs.json` records 422 local build-input hashes, all checked against the host copy. The source revision is the publication base plus the two-file delta (and its exact SHA pins); the eventual refactor commit supplies the immutable extraction revision. `#print axioms`: not applicable to these Rust/SBF gates.

The retry binary and its receipt completed successfully. The outer gates.sh shell subsequently exited 2 with an unterminated-quote message because another task-local harness edit changed that script while this shell was still reading it. The final script passes `sh -n`. The completed binary was not rerun: its exit-0 receipt and 8/8 JSON are retained. No claim relies on the wrapper exit.

## Stage 2 extraction

Refactor commit: `7d4c136f0`. Rooted at actual `crate::verifier::candidate::tx2_authenticated`, using the same pinned Charon (daad69be…), driver (efdbe5b8…) and extended-static Aeneas (4632746d…) as stage 1. No synthetic caller or helper-only body is substituted. The 78-declaration input inventory includes the adapter as a source pin; account/SDK adapter behavior remains outside the selected root. Field arithmetic, allocation, weights, dot kernels, domain arithmetic, observer trace and hashing are explicit backend frontiers. Charon succeeded with `has_errors=false`; Aeneas failed before Lean emission. No generated fact claimed.

### Extraction gate failure and stop

| Target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Actual refactored crate → Charon LLBC | 0 | 130.673 | 548,016 | 0 |
| LLBC → pinned extended-static Aeneas | 2 | 1.191 | 124,960 | 0 |

Source revision: `7d4c136f0` (full revision in the extraction input JSON and manifest). LLBC SHA-256 `1bb25f41eca431b098aef4160c9c1d10e0a86af8169b0f1bc577369ac7068df5`, 6,229,463 bytes, `has_errors=false`. `pins/llbc.json` indexes actual crate function bodies: the entry, common caller, resume, query loop body, accumulation, both finish helpers, finish_relation, polynomial, Merkle batch/node-count/verification and parser all have bodies, not opaque replacements. The LLBC stays on the host.

Aeneas error (exact): **There should be no bottoms in the value**. Source: `crates/aspis-r1-cost-probe/src/candidate.rs`, span **237:20–237:22**, the `&a` argument of `finish_relation(&v, &p, &a, obs)`, after moving out the fields, finishing weights and reconstructing `a`. Compiler source: `interp/InterpExpressions.ml:55`. The move/reconstruction refactor therefore does **not** solve the pinned translator's post-finish accumulator problem. This failure is not memory pressure and was not rerun or retried with another tool/cap. See `receipts/extract-aeneas/{stdout,stderr}.log` and both phase input JSONs for commands and exact tools.

Per the mandate, work stops at stage 2. No generated Lean files were emitted; no Lean compilation or `#print axioms` run occurred (N/A). Length equality, whole-resume proof-digest equality and the 12-query ordered-call theorem are all still obligations. Runtime traces supply regression evidence only. The stage-1 refactor is retained as a runtime-gated candidate, not an accepted whole-cone extraction or a formal source/model refinement. R13/R12, R15, R19 and S8 remain open.

## Source-changing continuation

The original span was misidentified above: zero-based columns 237:20–22 are
`&v`, not `&a`. The continuation authorized by the lead repairs that borrow
and subsequent whole-cone loan joins. Pinned Aeneas now emits the full cone;
local first shape facts and later runtime evidence are tracked separately in
`../stage2-continuation-20261020/REPORT.md`. The measurements and failure in
this historical packet remain bound to its old source and ELF.
