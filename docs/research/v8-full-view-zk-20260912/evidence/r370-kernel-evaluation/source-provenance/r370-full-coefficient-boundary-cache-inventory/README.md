# R370 `FullCoefficientBoundary` host cache inventory

Read-only inventory prepared from local tracked sources and the pinned host. No Lean process, compilation, or cache mutation was run for this inventory.

- Root module: `AspisV8R19.FullCoefficientBoundary`.
- Host source root: `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`.
- Host Aspis cache: `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`.
- External Mathlib source/cache path used for direct imports: `/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib` and `/home/dombarker/weighted-hensel-repair/.lake/packages/mathlib/.lake/build/lib/lean`.
- Toolchain recorded by the pinned focus workspace: Lean 4.32.0. Its source root has no repository `lakefile`/manifest; the saved focus workspace manifest has an empty package list. Existing focused commands set `-R` to the pinned source root and output `.olean` files into the cache `lib` directory.
- Source closure contains 60 `Aspis*` modules (including `AspisFormal`). All have cached `.olean` objects. Of these, 60 host `.lean` source files are byte-identical to the local tracked copy; mismatches: none.
- Direct non-Aspis imports: 25 modules. Presence and byte sizes/hashes are recorded in `inventory.json`; missing files are listed there. The direct external imports are `Mathlib` modules. Full transitive Mathlib import closure was not expanded by source parsing here.
- `FullCoefficientBoundary.olean`: SHA256 `ef1344f151b98fae82f38b847e082aef4f4b58426773f8c88246a7e62b15be1c`, 251568 bytes. Source SHA256 `66a7897879924c0f4dc99692e84cc9812104009a95e68e6c6908ef78fc7b136d`, 2753 bytes; tracked SHA256 `66a7897879924c0f4dc99692e84cc9812104009a95e68e6c6908ef78fc7b136d`.

## Coefficient kernel excerpt

See `source-excerpts.txt` (its SHA256 is `9739aeece0fd1abbc0d93e272c54c8fcabbd9328bd31354f56c1732e88a776c7`). In `FullCoefficientBoundary.lean`, `coefficient_blocks` (lines 11–25) exposes the block coefficient as a triple sum whose condition is `s.val + (4 - t.val) % 4 = k`, with `quarter` as the selected coefficient. `BetaUniformCorrection.lean` defines `sourceKernel` at lines 78–80 using that same condition. Its adjacent comment at lines 75–77 explicitly describes the reversed dual slot convention. `coefficient` itself is the ordinary `C i j * q i * w j` double sum at lines 45–46. These are the source/model declarations to document the requested coefficient identity scope; this inventory makes no additional semantic or theorem claim.

## Inventory integrity

- `inventory.json` SHA256: `104a6e938c4d5a91359136ffd20e4420a77791d764d996c19414315d367467a2`.
- `source-excerpts.txt` SHA256: `9739aeece0fd1abbc0d93e272c54c8fcabbd9328bd31354f56c1732e88a776c7`.
- Local Git revision at inspection: `7c588ebcd62955448a0298b3d480aa7e23c408bb`.
- Remote probe used SSH BatchMode, disabled host-key persistence, and only `sha256sum`, `wc`, directory listing, and `lake env printenv`/configuration reads.
