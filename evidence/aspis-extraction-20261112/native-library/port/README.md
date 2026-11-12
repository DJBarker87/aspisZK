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

## Compile under Lean 4.36.0-rc2

How each module is compiled (`host/fv_x6_compile.sh`, driven by `host/fv_x6_job.sh`):
- one module at a time, `lean -j1 -M7000 -DElab.async=false`, objects in `W/x6/objs`, each run in one `fv_slot.sh`
  scope (MemoryHigh 6G, MemoryMax 8G, no swap);
- LEAN_PATH: `W/x6/objs`, then X3's stage A library objects by reference. No L187 directory is on it.
- A module whose source sha256 and in-table dependencies are equal to X3's pass 2 has its objects copied (`cp`)
  from `W/x3/pass2` (227 modules).
- Resume key: sha256 over source, imports and the keys of the dependencies. An unchanged failure is never rerun
  (`fail/` markers).
- The table follows the ported tree (`host/fv_x6_table.py`).

Runs (one slot at a time; each wall time and peak RSS is the slot's `time -v`, the peak being the largest single
module or diagnostic):

| Attempt | Exit | Wall | Peak RSS kB | Memory events | Compiled+reused / failed / skipped |
|---|---|---|---|---|---|
| X6-p1 | 0 | 8:46.97 | 7,168,652 | none | 323 / 17 / 1,053 |
| X6-p2 | 0 | 5:54.14 | 7,168,684 | none | 413 / 15 / 964 |
| X6-p3 | 0 | 5:25.02 | 7,168,616 | none | 498 / 9 / 885 |
| X6-p4 | 0 | 5:20.23 | 3,483,040 | none | 628 / 5 / 759 |
| X6-p5 | 0 | 10:07.45 | 7,168,684 | none | 649 / 3 / 743 |
| X6-p6 | 0 | 9:27.50 | 7,168,780 | none | 698 / 5 / 689 |
| X6-p7 | 0 | 6:01.17 | 3,421,468 | none | 717 / 5 / 670 |
| X6-p8 | 0 | 6:01.60 | 3,461,644 | none | 729 / 4 / 659 |
| X6-p9 | 0 | 6:12.77 | 3,441,688 | none | 729 / 4 / 659 |
| X6-p10 | 0 | 6:36.56 | 3,571,436 | none | 759 / 4 / 629 |

The 7.17 GB peaks are kernel-memory failures, each run once (the three cases below and the step-split
diagnostics); `-M7000` stopped them inside the cap. Rows per module: `port-compile.tsv`.

## Totals (after X6-p10, `port-compile.tsv`)

- Modules in the set: 1,393. One vendored file was removed by lead decision, leaving 1,392 compiled modules.
- Compiled unchanged: 722 (495 compiled here, 227 with objects copied from X3 pass 2).
- Patched and compiling: 37. With the removed file and `R0.PolynomialPair` (patched, still failing) that makes 39
  patch rows in `port-patches.tsv`. Classes (a module can carry two):
  - simp set: 10;
  - rewrite or equation lemma: 6;
  - kernel recursion: 5 (`ExactTowerFinite`, `M31RetryOutputMassNat`, `M31EightLimbAbortBound`,
    `GSActualEncoderGRSBridge`, `CircleFibreRoots`);
  - elaborator or simp recursion: 4;
  - lemma renamed or Mathlib API change: 4;
  - vendored, upstream proof text: 6;
  - vendored, upstream reducibility attribute: 3;
  - type class or definitional unfolding: 1;
  - tactic closes earlier: 2;
  - vendored, declaration now in Mathlib: 2 (file removed, import line);
  - statement text, Mathlib API rename: 1;
  - added Mathlib import: 1.
- Failing: 4, all elaborator "maximum recursion depth" at the first tactic of a proof.
  - `R0.PolynomialPair`: patched twice, not yet fixed. The diagnostics show `Fin.foldr.loop` unfolded 479 times:
    Finset.univ of Fin 512 is built while a 512-term `monomialPolynomial` sum is reduced. The trigger inside the
    `truncate_eq` step is not yet identified; every piece of the step passes as a separate `example`.
  - `R0.ListsResponses`: not examined.
  - `R1InitialResponses`: not examined.
  - `InitialMessageComputableV8`: not examined.

  The last three became reachable only in X6-p10; they are probably the same family.
- Skipped behind them: 629 modules, `AspisFailureBoundModel` included.
- Error sites fixed: about 70 over the 39 modules (the first error of each module is in `port-compile.tsv`; the
  sites are the hunks of `port-patches/`).

Estimate of what remains:
- the R0 recursion family (4 known modules), plus whatever the 629 skipped modules hold;
- up to X6-p10 each pass uncovered 1 to 4 new failing modules per 30 to 60 newly compiled, so roughly 10 to 30
  further sites before `AspisFailureBoundModel` is reached; this is an estimate, not a measurement.

**AspisFailureBoundModel does not compile under 4.36.0-rc2 yet.** Statement checks (a), (b) and (d) need its object
and were not run under the new toolchain. Check (c) was run (below).

## Failure kinds, one example each

- **simp set:** `FS2.DuplexTrace.firstReads_eq_card`. simp unfolded `put` inside a `Finset.filter` predicate before
  `Finset.mem_filter` fired on the outer filter. Under 4.36 `mem_filter` then no longer matches, because the
  filter's `DecidablePred` instance still names `put`. The fix rewrites membership first and unfolds `put` after.
- **rewrite or equation lemma:** `R1PublicInitFrame.row0_bytes`, "Failed to rewrite using equation theorems for
  `absorbA`". Its hypothesis argument has type `5 ≤ p.D`, not syntactically `emptyRecord.length ≤ p.D`; the fix is
  `unfold absorbA`.
- **lemma renamed or API change:** `FiniteFieldNormalizedRootFactor`. `FiniteField.X_pow_card_sub_X_natDegree_eq`
  is now a deprecated alias with the ring argument implicit, so the explicit `K` is dropped.
- **definitional unfolding:** `V5FriInitialCircleEncoderIdentity`. `hcircleX` is stated over `Fin layer1Symbols`,
  the goal is over `Fin 131072`, and simp no longer unifies the two; the hypothesis is instantiated at `i`.
- **type class:** `V5FriInitialCircleEncoderIdentity.halfTurn_point`. The `Decidable` instance for equality in the
  circle subtype is not found; the fix is `Subtype.ext (by decide)`, the same 30-squaring computation as before.
- **tactic closes earlier:** `R1AppendCopyLinks`, where `convert` now closes the goal; the following tactics run
  under `all_goals`.
- **vendored:** CompPoly upstream v4.35.0 (06686e4c) proof text and attributes, taken under the lead's rule and
  recorded with file and line in `port-classification.tsv`.

## Kernel and elaborator cases: the reduction shape avoided

No limit was raised and no failed module was rerun unchanged. Each case was split into step diagnostics
(`diag-out/*` on the host) before the proof was changed.

1. **`AspisV8R15.ExactTowerFinite.cm31Exact_card`**: kernel "excessive memory consumption", 61.6 s, 7.17 GB.
   - Step split: each calc step passes alone, and the `Nat.card` route passes.
   - Shape: after `rw [Fintype.card_prod, ZMod.card]` the kernel must compare `*`-products whose arguments are
     `Fintype.card` of `ZMod 2147483647` in two spellings (`M31Exact` vs `ZMod P`). The kernel's Nat-literal
     shortcut whnf's the arguments, which unfolds `Fintype.card` into a list of 2^31 − 1 elements.
   - Fix: count through `Nat.card` (`Fintype.card_eq_nat_card`, `Nat.card_congr`, `Nat.card_prod`,
     `Nat.card_zmod`). No Fintype instance of the large type is compared.
   - 4.32 compiles the patched proof too.
2. **`M31RetryOutputMassNat.natOutputMass_eq_P_mul_base`**: the same message, 62 s.
   - Step split: `Fintype.card Value = P31 := Fintype.card_fin _` passes.
   - The steps that fail compare a `•` (`nsmul` with count P31 = 2^31 − 1) or a `Fintype.card (Fin P31)` term in
     two spellings or instance paths; the kernel unfolds `P31 • c` as repeated addition, or the card as a list.
   - Fix: `Finset.sum_const_nat` (a product, no `•`), then a rewrite with the count stated on the goal's own
     spelling (`show Fintype.card Value = P31 from Fintype.card_fin P31`).
3. **`M31EightLimbAbortBound.eightAbort_card_exact`**: kernel memory, 7.17 GB.
   - Step split: only the `Fintype.card_subtype_compl` step under three `letI` Fintype instances on
     `Fin 8 → RetryInput` (2^4096 elements) fails.
   - Shape: identifying two Fintype instance terms of that type needs `Finset.univ`.
   - Fix: `Nat.card_congr (Equiv.sumCompl _)` and `Nat.card_sum`, whose `Finite` instances are propositions, then
     `Nat.eq_sub_of_add_eq'`.
   - In `eightAbortMass_exact` of the same module, `simpa [..]` normalised the 2^4096-sized literals and hit the
     elaborator recursion limit; it is replaced by the term `eightAbort_card_exact`, which needs only unfolding of
     let-bound names and two defs.
4. **`AspisFormal.CircleFibreRoots`** `instance : Fact (Nat.Prime P)`, P = 2^31 − 1: kernel deep recursion.
   - Shape: the `norm_num` certificate is a chain of `MinFacHelper` steps up to √P. In the diagnostic it passes
     with `maxRecDepth` 2000, 8000 or 20000 and fails at the default; the raised values were used only in the
     diagnostic, never in a patch.
   - Under 4.32 the same term passed at the default, so the 4.36 kernel now enforces `maxRecDepth` on it.
   - Fix (lead decision): the Lucas–Lehmer certificate `lucas_lehmer_sufficiency 31 (by norm_num) (by norm_num)`,
     a 29-step residue computed with GMP arithmetic, with the added import `Mathlib.NumberTheory.LucasLehmer`.
     It does not compile under 4.32 (that Mathlib lacks the extension or the name in this form; unchecked which).
5. **`GSActualEncoderGRSBridge.{initial,final}_encode_degreeLt`**: kernel deep recursion.
   - Shape: `WithBot.coe_lt_coe.mpr h` with `h : natDegree < 1025` (resp. 256) has to be identified with the
     goal's numeral in `WithBot ℕ`, and the kernel unfolds the cast of the literal.
   - Fix: `exact_mod_cast`, i.e. cast lemmas instead of unfolding.
6. **Elaborator recursion on `monomialPolynomial` over Fin 512/513** (`WideExactInitialCirclePairInverseV5`, fixed;
   `R0.PolynomialPair`, open):
   - Diagnostics show `Fin.foldr.loop` unfolded 479 and 948 times: `Finset.univ` of `Fin 512` is built while the
     unifier reduces the sum.
   - WideExact: under 4.36 the numeral `(2 : K)` re-typed in the theorem elaborates through
     `Lean.Grind.CommRing.OfCommSemiring.instOfNatQ`, so the lambda differs from the one inside `oddPart`.
   - Fix: never re-elaborate the lambda (`unfold`, `_`, `conv_lhs => rw [.. monomialPolynomial_coeff]`).

Pre-existing raised limits in the carried source: `preexisting-limits.tsv` lists every `set_option maxRecDepth` (72)
and `maxHeartbeats` (46) line in the carried set, in 58 modules, with module and line. This includes
`AspisFormal.CircleGroupOrder:22` and `AspisV8R15.ExactTowerBase:10` (`maxRecDepth 20000`), which carry the same
primality proof. The optional "limit removed" patches for those two were not made.

## Lead decisions applied (2026-11-12)

1. **Vendored declaration now in Mathlib** (`Polynomial.smul_divByMonic`): see the section above.
2. **Added Mathlib import:** `AspisFormal.CircleFibreRoots` gains `import Mathlib.NumberTheory.LucasLehmer` (lemma
   `lucas_lehmer_sufficiency` and its norm_num extension). It is the only import added; it brings only Mathlib
   modules into the closure.
3. **Upstream reducibility attribute** (vendored only), exactly as upstream v4.35.0 06686e4c has it:
   - `CPolynomial` (Univariate/Basic.lean:58, `@[expose, implicit_reducible]`);
   - `CBivariate` (Bivariate/Basic.lean:34);
   - `Domain.n` (NTT/Domain.lean:37).

   Types and values are unchanged. Check (1): of the 42 carried modules that mention `Domain.n`/`D.n`/
   `CBivariate`, none that compiled before the attributes failed after them; 10 newly compiled and 3 failing ones
   compiled. Under 4.32 the two attribute-only files also compile. The statement comparison of the top theorems,
   check (b), is the decisive check that these attributes changed no meaning. It covers these edits and has not
   been run yet (see above).
4. **Statement text, Mathlib API rename:** `Wide.FactorBudgets.coeff_equivMvPolynomial`, changing
   `MvPolynomial.coeff M (equivMvPolynomial R polynomial)` to `(equivMvPolynomial R polynomial).coeff M`.
   - In Mathlib 9d581dff `MvPolynomial` is an abbrev for `AddMonoidAlgebra` and `MvPolynomial.coeff` does not exist.
   - Condition 3: under Lean 4.32.0 against X3's carried 4.32 objects, the `pp.all` printouts of the old text and
     the new text are byte-identical (sha256 db0c31f5a14b7491ddaf23b6f65cb3b35eb701a27cd271fb2bd7453ab0160aca, both).
     Files are in `statement-rename/`: the scratch sources, the 4.32 outputs, and the 4.36.0-rc2 printout of the new
     text for information, which uses `DFunLike.coe` of the AddMonoidAlgebra coefficient.
   - Scan (`removed-names-scan.tsv`, `host/fv_x6_removed_names.py`): over the whole carried set, the removed names
     the errors showed (`MvPolynomial.coeff`, `Nat.xor_eq_zero_iff`, `Polynomial.smul_divByMonic`) occur in a
     statement only here. The 7 other occurrences are in proof bodies. Modules not yet reached may use other removed
     names; that is unchecked.

## Statement checks

- (a) axioms, (b) statement printout against `checks-r6/check-b.txt` / `X5Statements.out`
  (f474e291bcb458ce09753aacea0fb34a2a4f2eea291bd62a00e44774d9c0c9cf), and (d) import closure: **not run**,
  because `AspisFailureBoundModel` does not compile yet. `host/fv_x6_checks.sh` and the check files (X3's, plus
  `X6Extra.lean`) are ready; the LEAN_PATH scan for kind (d) or omitted objects is part of the script.
- (c) **pass**. `host/fv_x6_stmtcheck.py` over all 38 changed modules plus the removed file, with the allowances
  `check-c-allowed-header.tsv` and `check-c-allowed-removals.txt`: 0 findings (`check-c.out`). How it works:
  - It compares each declaration's statement text (up to `:=`, `where` or a line-initial `|`), flags changed lines
    before a statement's last line, attribute lines without an allowance, and new header lines without an
    allowance, and searches added lines for sorry, admit, native_decide, maxHeartbeats, maxRecDepth, set_option,
    axiom and decide.
  - Planted violations are all caught: a changed hypothesis (`n < 33` to `n < 32`), a changed instance type
    (`Nat.Prime (P)`), an import not on the list, an unallowed `@[simp]` line, a dropped `@[simp]` on an allowed
    declaration, and an extra `simp` in an allowed attribute list.

## Patches that do not compile under Lean 4.32.0

Each patched module was compiled under 4.32.0 against X3's coherent 4.32 carried objects. As of X6-p9, these do not
compile under 4.32:
- the CompPoly upstream-text patches (`Raw.Proofs`, `ToPoly.Equiv`, `KernelInPlaceCorrectness`,
  `DivisionCorrectness`, `Lagrange`, `Roots.Correctness`, `Bivariate.Factor`): upstream wrote them for the newer
  Mathlib;
- `FiniteFieldNormalizedRootFactor`: the new argument convention;
- `CircleFibreRoots`: Lucas–Lehmer.

Every other patched module compiles under both toolchains (column `compiles_4_32_0`).

## Not done

- The remaining failures and everything behind them, so the model module, checks (a), (b), (d), the repository
  layout (`lean-lib/`, MANIFEST.tsv; `host/fv_x6_layout.py` and `host/fv_x6_rebuild.sh` are written but not run),
  and the rebuild timing.
- The optional limit-removal patches for `CircleGroupOrder` and `ExactTowerBase`.
- Whether CompPoly upstream has a v4.36.0-rc2 revision (no fetch was made).

## How to rerun

1. `bash W/x6/bin/fv_x6_pipeline.sh` regenerates `W/x6/carried-src`, and the manifest must equal the sha256 above.
2. Apply `port-patches/*.diff` to a copy as `W/x6/ported-src` (`patch -p0` from `W/x6`, then delete
   `CompPoly/ToMathlib/Polynomial/Div.lean`).
3. `bash W/fv_slot.sh X6-<new> 5400 bash W/x6/bin/fv_x6_job.sh <tag>`.
4. Check (c): `python3 host/fv_x6_stmtcheck.py carried-src ported-src check-c-allowed-removals.txt
   check-c-allowed-header.tsv`.


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
