# R372 SourceCircleBoundary cache inventory

Read-only cache/source follow-up to R370. This inventory filters the existing R370 host probes by the actual recursive Aspis import closure of `AspisV8R19.SourceCircleBoundary`; it did not compile or invoke Lean.

- Pinned source root: `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`.
- Pinned cache: `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`.
- Tracked source root: `/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922/docs/research/v8-full-view-zk-20260912/lean`.
- Closure: 52 Aspis/AspisFormal modules; cached local objects and host `.lean` sources all present and byte-matching the tracked copies (see `inventory.json`). Direct Mathlib imports: 25, with source and `.olean` present in the same external package cache path recorded by R370. No missing local or direct external objects.
- Cache resolution caveat persists from R370: the Mathlib package object files are present under the recorded external path, while `lake env printenv LEAN_PATH` for the focus workspace only showed the pinned `lib` and Lean toolchain paths. Object availability is recorded; active search-path linkage remains unverified.
- No compilation or cache mutation was performed.

## Source scope excerpt

`source-files-excerpts.txt` preserves the complete current tracked source bytes of `SourceCircleBoundary.lean`, `FullQuotientWeights.lean`, and `BetaUniformCorrection.lean` with hashes. The target module’s `column` definition and use of `coefficient_fold_zero` are captured there, together with the relevant imported coefficient/model declarations. This is source inventory only; no new premises or theorem conclusions are supplied.

## Integrity

- `inventory.json`: SHA256 `42def2145bc9f65cc759a7c681f683cc07d4a477da7328479f850303cb840db3`.
- `source-files-excerpts.txt`: SHA256 `8dd30c5e91f9676a1bb567766e02c851d902e1fe152ad8963c8a873acfd2f56f`.
- Prior reusable hash inventory: R370 `inventory.json` SHA256 `104a6e938c4d5a91359136ffd20e4420a77791d764d996c19414315d367467a2`.
- Local Git revision: `7c588ebcd62955448a0298b3d480aa7e23c408bb`.
