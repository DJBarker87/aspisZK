# Port of the carried library to Lean 4.36.0-rc2 (task X6)

Status: target not yet established. This is a toolchain port record. No statement was changed, nothing new is
proved, and a module that compiles is not thereby verified.

`W` = `~/project-offloads/future-version-20261111` on the build host. Host outputs are under `W/x6/`.

## Set-up

Toolchain of the translator's library, built by X3 under `W/x3/` and used by reference:
- Lean 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a);
- Mathlib 9d581dfff2e41de989072ea63abf3daf69311520;
- Aeneas library at 0d21a9ec7bbbb110110cacc14464a47fd71c8705.

The stage A objects come from `W/x3/aeneas-src/backends/lean/.lake` (Aeneas, Mathlib and the other packages of
its manifest).

Carried source set. `host/fv_x6_pipeline.sh` is `fv_x3_pipeline4.sh` with every output moved to `W/x6`. It reads
only X3's inputs:
- the library `aspis-lib6`, copied to `W/x6/aspis-lib6` because the pipeline writes `SHA256SUMS.host` and
  `bases/` into its library directory; every file hash equals `aspis-lib-r6.sha256`;
- the working lists `omit4.txt` and `drop-decls4.tsv`, copied to `W/x6/omit.txt` and `W/x6/drop-decls.tsv`
  (sha256 2e4b24746f175da7ad6f38c3dac345d24090dc387d70c0f5cf8f23bd0c29f1aa and
  3a06ff9c6f928449a3fec094cb3262f44cabb37f993d078ca0cc5716d6d58707, equal to `omit-modules-r6.txt` and
  `drop-decls-r6.tsv`);
- the chain sources `chain-src-d012`, the closure table, and the L187 sources, all read in place.

Two changes from X3's run:
1. Roots (`host/fv_x6_plan.py`): the carried set is the import closure of the 73 chain modules of
   `AspisFailureBoundModel` (`repoint/host-order-model-73.txt`). **33-row check: record of the two-transaction
   proof, not carried.** The modules `AspisRowStarts33`, `AspisChargedWeight`, `AspisChargedHitMass` and
   `AspisChargedHitMassCheck` are not in the set, and the closure of `Frozen2StartChargeProbability` is not added.
2. Every carried module is compiled under the new toolchain. X3's hardlinking of L187 objects is not done.

Result (`W/x6/carried-src`, copies, no links):

| Kind | Modules |
|---|---|
| Aspis chain | 73 |
| CompPoly (vendored) | 87 |
| earlier proof's maths, kind (c) | 1,226 |
| base modules | 7 |
| **total** | **1,393** |

The set has 198,205 lines. The gate (`closure/plan-gate.tsv`) has 0 violations.

- **Manifest**: `W/x6/MANIFEST.sha256`, one line `path<TAB>sha256` per file, sorted with `LC_ALL=C`; sha256 of
  the manifest file **02c661450ab9983d1d46aa1417a451e8cd76b8914a13a4a9f6ff5c3446929946**. Copy:
  `carried-manifest.sha256`.
- **Same as X3's final set:** all 1,393 files have the same sha256 as X3's revision-6 carried set (1,397 files).
  The four files of X3's set not in this one are the 33-row side modules.
- **Same as the repository chain:** the 73 chain files equal `docs/research/future-version/lean/*.lean` at
  6969d34e1f8 (0 differences).

FILL-IN: compile, totals, kernel cases, checks.

## Vendored declaration now in Mathlib: `Polynomial.smul_divByMonic` (lead decision 2026-11-12)

Under 4.36.0-rc2 `CompPoly.ToMathlib.Polynomial.Div` fails: "`Polynomial.smul_divByMonic` has already been
declared". The lead's decision was to remove the vendored declaration in favour of Mathlib's, following upstream.
The file holds that one declaration only, so it is removed from the carried set. Its one importer,
`CompPoly.Univariate.DivisionCorrectness`, has the import line `public import CompPoly.ToMathlib.Polynomial.Div`
replaced by the removed file's only import, `public import Mathlib.Algebra.Polynomial.RingDivision`. CompPoly
upstream v4.35.0 has exactly this line. The use site (`rw [←Polynomial.smul_eq_C_mul,
←Polynomial.smul_divByMonic]`, `DivisionCorrectness` line 549) is unchanged.

| | Vendored (CompPoly at the carried checkout 4165a87, `ToMathlib/Polynomial/Div.lean:25`) | Mathlib 9d581dfff2e4 (`Mathlib/Algebra/Polynomial/RingDivision.lean:63`) |
|---|---|---|
| statement | `theorem smul_divByMonic {R : Type*} [CommRing R] (c : R) (p q : R[X]) : c • p /ₘ q = c • (p /ₘ q)` | `theorem smul_divByMonic (c : R) (p : R[X]) : c • p /ₘ q = c • (p /ₘ q)` under `variable {R : Type u} ... [CommRing R] {p q : R[X]}` (lines 33, 37) |
| namespace | `Polynomial` | `Polynomial` |
| difference | `q` explicit | `q` implicit (section variable); otherwise the same equation |

The file header's own note reads: "Note, there's a PR to Mathlib that includes this result and this file should be
deleted if/when that PR is accepted: https://github.com/leanprover-community/mathlib4/pull/39868". CompPoly
upstream v4.35.0 (commit 06686e4c70939af82203af21516f8ab8a21a8051, the local clone X3 prepared) has no
`ToMathlib/Polynomial/Div.lean`, and its `DivisionCorrectness` imports `Mathlib.Algebra.Polynomial.RingDivision`.
The clone holds a source export without `.git`, so the commit that deleted the file cannot be named from it; the
deletion is visible at v4.35.0 and absent at 4165a87. Recorded in `port-patches.tsv` as kind `vendored:
declaration now in Mathlib` (two rows: the removed file and the import line).
