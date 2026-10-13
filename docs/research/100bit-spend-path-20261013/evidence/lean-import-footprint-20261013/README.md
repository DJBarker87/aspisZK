# Focused Lean import-footprint and Line 18 geometry evidence

This evidence belongs to isolated NUC overlay `/home/dombarker/project-offloads/aspis-line18-import-footprint-20261013`, using Lean `leanprover/lean4:v4.32.0` and the pinned Mathlib/Aspis object cache shown in `environment-base.json`. No package-wide Lake build or manifest replay was run.

The ten copied `AspisFormal` modules change import declarations only: each previously had `import Mathlib`; the selected modules now import specific Mathlib definitions and tactics. The worktree diff for these ten files contains only import-block changes. Local comparison confirms their declaration and proof bodies are unchanged relative to the pre-copy worktree files. The exact original pinned-source revision/archive manifest was not captured before creating the NUC overlay, so this does not assert that the overlay source is byte-identical to a separately identified immutable historical revision.

The dependent focused route in `compile-order.txt` compiled through `AspisFormal/V7ExactOneFoldDomains`; the successful receipt for each latest green target is summarized in `compile-summary.json`. Failed API/plumbing attempts are preserved alongside the green attempts. The final `R1Line18Geometry` target compiles with `set_option autoImplicit false`; the additional signature check target confirms the concrete and algebraMap statements. `#print axioms` for both geometry theorems returned `[propext, Classical.choice, Quot.sound]`.

Final geometry source SHA256: `aea9a5746cc57820484e64b515704e18c0f882cf1e37cc8fb2201c5ac45c5bbd`. Its successful receipt records exit 0, wall time 27.76 s, max RSS 4,694,772 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean `-M5000`.

The exact focused compile invocation was:

```sh
cd /home/dombarker/project-offloads/aspis-line18-import-footprint-20261013
systemd-run --user --scope --quiet \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o evidence/R1Line18Geometry-g.time.log \
  /usr/bin/timeout 900 python3 run2.py environment-base.json objects sources \
  objects/R1Line18Geometry.olean sources/R1Line18Geometry.lean 5000
```

`run2.py` sets `LEAN_PATH` to the overlay objects followed by this exact base value:

```text
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/Cli/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/batteries/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/Qq/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/aesop/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/importGraph/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/plausible/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib/.lake/build/lib/lean:/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/build/lib/lean:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean
```

The final module object is `objects/R1Line18Geometry.olean`. The selected pinned ZK-v7 cache does not contain `Wide/FinalEncoder.olean`; that module was found in separate R0/wide caches, but was not layered into this overlay or checked for compatibility. Root/nuc inventory should resolve that in the downstream environment.
