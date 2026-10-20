# R22 V15 dependency source provenance addendum

This addendum records source provenance for the exact direct-import objects used by the already-green `R22RawQmProductResiduesV15` target. It does not rebuild or alter that target.

- The Mathlib checkout used by V15 is the pinned project package at commit `81a5d257c8e410db227a6665ed08f64fea08e997`, remote `https://github.com/leanprover-community/mathlib4`; remote status was clean at inspection. The captured Lean source files and their object hashes are listed in `manifest.json`.
- `QM31WordTower.lean` is copied from the exact source snapshot referenced by its accepted receipt, not inferred from the V15 importing workspace. That receipt identifies source base revision `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`, Lean 4.32, source/object hashes, and direct imports.
- Original V15 preflight and receipt remain in `/tmp/r22-raw-qm-product-residues-v15-20261020/attempt/proof-evidence/`; this addendum supplies the previously missing dependency source provenance only.
