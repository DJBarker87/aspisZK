# PCXA_ report: provenance snapshot (P6, first of two runs)

Scope. This is a snapshot over the provenance evidence merged at research 65f42e74c0d, on the ledger30 gate (base 6ce07a6a593) and the frozen source 4bb3b3f. It records provenance only. It changes no ledger row, trust row, RSL, security contract or shipped source, and it adds no trust row. Release replay, L187/L188 and source-to-ELF are out of scope. A large OPEN remainder is expected and is reported as such. The sibling P1f emissions were not used.

## 1. The deployed_splitB cone (headline)

The cone of AspisR1.TAS_FinalB.deployed_splitB has 146370 constants. The list is the pinned-walker output NNH_L942 (sha256 0b316cbb, verified), reused rather than recomputed. Mapped to emitted gate modules by the PCO ownership rule, the cone reaches 209 of the 373 emitted modules and 1612 annotated definitions.

Of those 1612 definitions, 258 are RECEIPTED (40 modules whose emission has a hash-linked receipt; the receipt's overflow configuration is not re-derived here), 435 have a Lean equality with a correct basis (EQUALITY_PROVED), 4 are EQUALITY_DOMAIN (loop-return refinements, not plain equalities), and 915 are OPEN. The OPEN definitions split into 547 with no overflow-correct fresh emission, 247 whose only record has a wrong basis (counted OPEN under the 2026-11-09 ruling), 81 failed or other, and 40 with no equality record. At module level 155 of the 209 modules are OPEN, 40 RECEIPTED, 5 fully EQUALITY_PROVED and 9 reach no annotated definition. No canonical-domain equality exists yet, so EQUALITY_DOMAIN in the usual sense is empty.

The Lean audit compiled the credited PRVEq files, plus the P4b and P4c final files, in 12 bundle scopes on the ledger30 gate export (L001-L012; 11 succeeded and one failed). All 493 credited theorem names were found, and every one of the 985 PRVEq constants audited depends only on propext, Classical.choice and Quot.sound. There is no sorry and no local axiom. Files that declare a common name sit in different bundles, so there is no single combined environment. L006 (bundle A6) failed on one S8OwnedP6 theorem that passes alone (L011); it was split into L011 and L012 and not rerun unchanged. The reason that theorem fails in a bundle context is unexplained and is a limit. Peak RSS was 6.0 GiB, no swap, no timeout, no cap raised. Wrong-basis theorems (177 proved definitions) were not audited and carry no credit.

## 2. Ledger30 view and rows

Over the 258 modules reached by CLOSED roots, the definition-level counts are 953 OPEN, 450 EQUALITY_PROVED, 374 RECEIPTED and 4 EQUALITY_DOMAIN. Of 599 CLOSED rows, 471 are conditional at definition level, 114 are clean at definition level, 12 reach no emitted module, and 2 have no root. At module level, 562 rows rely on a module whose rollup is OPEN (PCO gave 565 relying on any non-receipted module). The 114 clean rows are clean only with respect to the annotated definitions they reach; unannotated hand-written names they reach have no provenance status, and the hand models below are a separate condition. PCXA_PROVENANCE.json carries the per-row open modules.

## 3. R22 split

R22 (design/R22-OVERFLOW-20261021.md) owns the checked-to-wrapping direction. Provenance does not discharge it. By body class, the cone's 1612 definitions are 43 wrapping-configuration, 217 checked-configuration, 8 checked with some wrapping, and 1344 with no arithmetic in the body (configuration-independent in themselves). RPz7_FIo_NativeFuns mixes bodies and is classified per definition. The classes come from a text detector; PCUF's required configuration is carried as recorded. R22's packet cites frozen source b2727acd, not 4bb3b3f. I did not reconcile that.

## 4. Hand models

The union of all campaign hand-model files has 924 deduplicated entries. 245 are hand-written gate models, 191 of them matched by a cone constant of the same short name (an over-approximation). 601 are externals with no gate definition found in the examined files; these are open obligations, not models. The classes are SDK type models (a), the core slice iterator model (b), Option/Result combinators, array/slice, alloc and allocator, num/ops, discriminant helpers, S1 expand-values, and frozen-crate item models. PCXA_TRUST_PROPOSALS.md has proposed text only. S1ValuesOwnedModelV1 is in the cone (module hit, 7 rows). The cone reaches AspisR1.NOC_PrepareFront.values, LIBC_ExpandValuesModel.source, NFU_Retarget.compact.expand_values and AspisS1ValuesOwnedInstallation.expandValues (TAS_G0_AUDIT.json lead_provenance_check; that is presence in the cone, not a review of what NOC_PrepareFront.values states). The old RPx_Deployed cone lacked it. The NFU_LPl_Kit_FunsExternal name itself is not in the cone. ExpandValuesFrozenEq is unproved.

## 5. No-source cut modules, non-frozen sources, L187

All 24 no-source cut modules reach the cone and serve at least one row. PCXA_NOSOURCE.md lists constants, rows, rollup and the R and F costs per module; I did not choose. No Kani harness is recorded for any of them in the PCWB/PCWC files. I did not search for one exhaustively.

The non-frozen detector flagged 28 modules (26 in the cone). AspisR72Sampler.Funs is identified: its M31.mul canonical fast path is blob a47a9996aa63 of src/field.rs under evidence/r72-sampler/selected/source (first commit 0319ac2b7b5), which matches 31 of 32 doc-comment ranges and the gate body. The detector cannot see a changed body behind unchanged line ranges. The unflagged modules are not shown frozen. The M31.mul equality remains an OPEN P3 item.

L187 comparison, by source sha256 and not by object (L187 compares declarations; the .olean embeds its invocation path). Of the 14 unrecovered modules, 12 are in our partition and all 12 pick the same hash-matched candidate; 2 are not emitted modules. None of the 14 has a credited provenance equality. Of the 42 versioned or renamed modules, 10 are emitted and agree. Of the 159 modules with no or several sources, 73 are emitted and agree. Of the lead's eight SOURCE_PATH_DIFFERS modules, four agree, two are not emitted modules, and two (AspisR1WideToBytesSource.Funs, ClaimsUnrolledParentTypes) have a primary partition candidate equal to the old committed source and agree only through the PCO shadow candidate or control. Equality statements are against compiled constants, so they are unaffected. The file L187_SOURCE_FIXES.jsonl was read from branch codex/cx-integrate-20261107.

## 6. Inferred facts

* The gate's extraction feature set is inferred (PCQF-C3), not recorded.
* Two toolchain labels are in the record: the Charon driver at nightly-2026-06-01 and RUSTUP_TOOLCHAIN nightly-2026-09-17 (P4b E001 and NJT used the latter, rustc 1.100.0-nightly; the overflow-ON runs used the former, 1.98.0-nightly). Both are kept per definition where known.
* Emissions come from two Aeneas builds: the original (959659a6, rebuilt by P4c) and aeneas-b59d5188-extended. The tool is recorded per definition.
* The gate M31.mul comes from an older field.rs (the AspisR72Sampler line) and is an OPEN P3 item.
* Required configuration per definition is PCUF's value, not recomputed independently.

Target not yet established.
