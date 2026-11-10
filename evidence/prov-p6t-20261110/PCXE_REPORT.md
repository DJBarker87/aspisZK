# PCXE_ report: provenance, P6 refresh 2 (recount after P1i, P3f to P3l and the trust-row naming)

Scope. Provenance only, over the evidence on research at 74a3cf93287 (P1i, P1j, P3f, P3g, P3h, P3i, P3k, P3l on top of the PCXD_ inputs), frozen source 4bb3b3f, ledger30 gate. No ledger row, trust row, RSL, security contract or shipped source changed, no trust row entered, nothing pushed or merged. evidence/prov-p3m-20261110 is not merged on research, so it is not used. Outside this report: the release replay, L187/L188 (source reconciliation only), R22 (it owns checked versus wrapping) and source-to-ELF.

## 1. Headline: AspisR1.TAS_FinalB.deployed_splitB

The cone has 146370 constants (pinned list, hash verified; the reach step reproduced the same 209 emitted modules and 3204 reached names). It reaches 1707 definitions that carry a status:

* EQUALITY_PROVED 920; RECEIPTED 256; EQUALITY_DOMAIN 6; CONDITIONAL_ON_BINDING 43; DEPENDS_ON_LIBRARY_TRUST 7; HAND_ADAPTED 5; NO_FROZEN_COUNTERPART 4; OPEN 466.
* OPEN splits into 263 with no overflow-correct fresh emission, 146 failed or other, 40 with no record, and 17 wrong-basis (counted OPEN, unchanged).
* Module rollups over 209 modules: 115 OPEN, 40 RECEIPTED, 38 EQUALITY_PROVED, 5 CONDITIONAL, 2 DEPENDS_ON_LIBRARY_TRUST, 9 reach no annotated definition.

Inside the 920: 753 are on an overflow-ON emission, 84 OFF, 2 OFF-default and 81 are Types records with no arithmetic configuration; 69 are Equiv isomorphisms of Types declarations, not term equalities. The ShrAmt-dependent set is unchanged (33 EQUALITY_PROVED and 2 EQUALITY_DOMAIN, verified for overflow-checks-off only). RECEIPTED still means a hash-linked extraction receipt whose overflow configuration is not re-derived here.

The 43 CONDITIONAL records are binding results, not proofs of the deployed path: the theorem quantifies over an Ext and Bound record (the emission's opaque callees against their gate counterparts) and the deployed Ops instance is not shown to satisfy Bound. They are AdapterRw (13: P3f 8, P3k 5), CurrentCompactCaller (8: OFF_* five, prepare, tx1, LOGICAL_SEMANTIC), Port3 closures (8), S1NativeCompact expand_semantic (3), Port5Q2 weights (2), NMT (3), VTop tx2_common and tx2_authenticated (2), and the P3d transport results (4 left after two moved to the trust class). The top verifier results (stage1_owned, stage2_owned, prepare, tx1, tx2_common, tx2_authenticated) are therefore CONDITIONAL_ON_BINDING; VTop tx1 stays OPEN.

The 7 DEPENDS_ON_LIBRARY_TRUST records, each with its row named (PCXE_TRUST_NAMING.json): the four WideToBytes definitions (HM-B; no Lean equality exists for them and the Aspis-side loop arithmetic is not separated, so this is the weakest member of the class), Port23PUSH push and update_residue_row (HM-B; the theorem holds for every into_iter and only that the parameter is the library into_iter is outstanding), and selected_claim (CrossCrateConstantEncoding). This class is counted separately and never as proved. WideExact.from_le_bytes is EQUALITY_PROVED (PCVH_L008, all inputs).

The 599-row ledger30 view, recomputed from the committed tables (PCXE_ROW_TABLES.json, same method as PCXD_): 180 clean at definition level, 405 conditional, 12 reach no emitted module, 2 rootless. "Clean" is over annotated names only; hand-written names and hand models are outside it, and 554 rows still rely on a module whose rollup is OPEN. A row counts clean only if every annotated definition it reaches is RECEIPTED, EQUALITY_PROVED or EQUALITY_DOMAIN, so CONDITIONAL and DEPENDS records keep a row conditional.

## 2. Delta from PCXD_

| quantity | PCXD_ | PCXE_ | why |
|---|---|---|---|
| EQUALITY_PROVED (cone defs) | 848 | 920 | +72: P1i 49, P3h 8, P3i 4 (FIp four_dots loops), P3f 11 (Option.ok_or, ten Port3 closures) |
| CONDITIONAL_ON_BINDING | 6 | 43 | +37 net: P3f 25 (AdapterRw, caller OFF_*, Port3, Port5Q2, NMT), P3k 8, P3i 4, P3l 2, less 2 moved to the trust class |
| DEPENDS_ON_LIBRARY_TRUST | 0 | 7 | new class: WideToBytes 4, Port23PUSH 2, selected_claim 1 |
| HAND_ADAPTED | 33 | 5 | 28 moved to proved or conditional |
| OPEN | 554 | 466 | 88 fewer; wrong-basis 17 unchanged |
| OPEN, no overflow-correct emission | 325 | 263 | P1i and P3h |
| modules rolled up OPEN / EQUALITY_PROVED | 133 / 26 | 115 / 38 | |
| clean rows / conditional rows | 163 / 422 | 180 / 405 | same row rule |
| rows relying on an OPEN module | 561 | 554 | |
| combined import | 17 bundles, 251 files, 2472 theorems | 21 bundles, 292 files, 4812 theorems | see section 3 |
| hand models; externals a / b / c | 245; 502 / 0 / 99 | 245; 502 / 0 / 99 | none added; c now split |
| no-source cut modules OPEN | 20 of 24 | 19 of 24 | CurrentWideMulCanonical complete |

Nothing moved from proved to open. 21 CONDITIONAL records and 5 DEPENDS records moved from OPEN, 18 CONDITIONAL and 10 EQUALITY_PROVED from HAND_ADAPTED.

## 3. Combined import and audit

PRVCmb_ROOT imports PRVH_WrapAdd and bundles C01..C21. C01..C17 are the PCXD_/PCXB_/PCXC_ objects reused by reference (pinned by sha256 in the root receipt); I compiled C18..C21 (the 42 new credited files) and the root. Eight Lean scopes: L001 C18, L003 C19, L005 C20, L006 C21, L007 and L008 root all exit 0 (longest 60 s, peak RSS 6.3 GiB, swap 0, caps unraised); L002 and L004 failed on defects of my bundler, not of any proof (a credited file leaves a namespace open at end of file; three P3k files declare identical root-level helper lemma names). Each was fixed by changing the bundler (PCXE-C13) with the earlier bundles byte-identical, not rerun unchanged. L007 audited 3710 constants and missed three credited theorem names because the audit selected only names rooted at PRV/PCVE/PCVB, which skips theorems declared inside a gate namespace. That gap also existed in the PCXD_ audit (3340 constants). L008 adds the infix patterns: 13099 constants audited, 4812 theorems one by one, each depending only on propext, Classical.choice and Quot.sound, no local axiom declaration, and all 1058 credited theorem records found by name. No sorry, native_decide or axiom in any credited file. Generated heartbeat limits are at or below the Aeneas default. Excluded: files that prove only superseded, wrong-basis or open records (419) and scratch with sorry.

## 4. Provenance, R22, hand models, externals, non-frozen, L187

R22 split of the definition bodies is unchanged (51 wrapping, 217 checked, 8 checked with some wrapping, 1431 without arithmetic); Port3's ten new equalities are on the OFF emission by the per-definition rule. Hand models: 245 hand-written gate models, none added by P1i or P3f to P3l. Externals without a gate definition: 502 resolve elsewhere, none is covered by an existing trust row, 99 unresolved: 68 aspis-frozen (41 distinct names) stay open obligations; 31 library or SDK entries name a proposed row (HM-A 16, HM-D 14, HM-F 1) and are counted in the named-not-proved family. solana_sdk_ids bpf_loader_upgradeable.id is not named in the HM-A text today. Non-frozen cone modules: all 26 are OPEN under the owner decision of 2026-11-10 unless a fresh 4bb3b3f extraction equality holds for every definition; 4 meet that at definition level, 22 do not (21 detector-blind, 1 open). L187: the flag on AspisR1PublicPreparation/Funs.lean is settled: the committed copy with sha256 544b75b9 equals all 87 compiled constants (PCVJ_L003); the other L187 lists reconcile as in PCXD_.

PublicPreparation (P3l, 26 definitions fresh 4bb3b3f text = gate): 20 EQUALITY_PROVED, six DEPENDS on HM-C (map_err), three of them also on ReviewedTranscription-PublicPreparation.public_bytes, whose gate was emitted from a mirror crate, not the frozen file. The headline cone reaches one constant of that module, so none of the 26 enters the section 1 totals.

## 5. Not established

Not established: 466 OPEN cone definitions (263 need an extraction), 17 wrong-basis, the 43 binding results (each needs the deployed instance shown to satisfy Bound, one fresh=gate theorem per Ext callee), the 7 trust-class records, 5 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, 19 of 24 no-source modules, 22 of 26 non-frozen modules, 68 aspis-frozen externals, the 23 array_from_fn dependants (the emission declares core.array.from_fn as an axiom, so no bridge is derivable), and everything outside provenance. Two P1i records the earlier job called library-dependent (derived PartialEq on QM31 and WideExact) and NID resume stay OPEN: no row names them.

Target not yet established.
