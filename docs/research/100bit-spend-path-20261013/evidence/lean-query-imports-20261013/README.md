# Q22 Lean import-cone replay evidence

Root target: `R0C.V3.Q22Law`. This was a bounded, focused replay of the 36 custom-module import closure using the pinned NUC cache. It was not a package-wide replay or a security/probability conclusion.

Local git base: `3638d7546f6e03a1afb0eaabdb1cff38d1631e84`. The runner used Lean `leanprover/lean4:v4.32.0`, 4 GiB MemoryHigh / 6 GiB MemoryMax / no swap, with `-M5000`; every per-target resource receipt and Lean log is archived.

The only source changes in this task were direct import declarations. The seven edited files and body-hash comparisons are in `closure-manifest.json`; each non-import body hash matches `HEAD`. The resulting narrow imports are:

- `AspisV8R19/OracleResampling`: `Mathlib.Algebra.BigOperators.Field`, `Mathlib.Tactic.Ring`, and `Mathlib.Tactic.NormNum` replacing broad `Mathlib.Tactic`; the first focused attempt exposed missing `Finset.sum_div`, fixed by the exact defining module.
- `AspisV8R19/DuplexFrames`: `Lean.Elab.Tactic.Omega` replacing broad `Mathlib.Tactic`.
- `AspisV8R19/CausalFirstHitUnionBound`: `Mathlib.Algebra.Order.BigOperators.Group.Finset` for `single_le_sum` and `sum_le_sum`.
- `AspisV8R19/R413GuardedOracleDistance`: `Mathlib.Algebra.Order.BigOperators.Group.Finset`, `Mathlib.Algebra.Order.Field.Basic`, and `Mathlib.Tactic.Linarith`.
- `AspisV8R19/R417Q22SuccessLaw`: `Mathlib.Tactic.FieldSimp`.
- `FS/LemmaA`: `Mathlib.Tactic.Linarith`.
- `FS/Theorem`: `Mathlib.Logic.Equiv.Fin.Basic` for `finSumFinEquiv`.

The first `SourceDuplexStep` attempt found the expected namespace-first cache shadowing gap for `AspisV8R19.DuplexFreshPair`. A workspace symlink was added to the exact pinned generic-cache object; its source SHA matches the archived r73 metadata pin and its object SHA is recorded in the manifest. The following compile passed.

The archived attempts include initial failures as well as successful focused retries. Failures were caused by missing direct imports or the namespace shadowing gap; no theorem proof bodies were edited. All successful changed/downstream targets printed axioms without `sorryAx`; only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) appeared where present.

Artifacts: `remote-artifacts.tar.gz` contains the selected runner receipts/logs, freshly generated workspace oleans, and four pinned leaf oleans. `source-snapshot/` freezes the 36 custom source files. `closure-manifest.json` records source/object hashes, dependency imports, selected successful receipts, and failed attempts. `receipts-index.json` indexes all captured attempts.

The repository ignores loose `.olean` files. They are retained inside the
tracked `remote-artifacts.tar.gz`; after a fresh checkout, restore them with
`tar -xzf remote-artifacts.tar.gz -C archive` from this evidence directory
before running `sha256sum -c SHA256SUMS` from the repository root. The archive
contains only this task's formal sources/build evidence; no wallet material.
