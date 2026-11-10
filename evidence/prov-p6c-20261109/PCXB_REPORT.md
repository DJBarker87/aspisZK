# PCXB_ report: provenance, complete P6 (second run)

Scope. Provenance only, over the evidence on research at 54d05e1e61d plus the P3e (PCVE_, research 3ba71246350) file and the NPE_ ShrAmt check. Ledger30 gate (base 6ce07a6a593), frozen source 4bb3b3f. No ledger row, trust row, RSL, security contract or shipped source changed; no trust row added. Release replay, L187/L188 and source-to-ELF are out of scope.

## 1. deployed_splitB cone (headline)

The cone of AspisR1.TAS_FinalB.deployed_splitB has 146370 constants (pinned walker list NNH_L942, hash verified, not recomputed). It reaches 209 of 373 emitted gate modules and 1707 definitions that carry a status. Status, from PCQH_ALL_STATUS.json (the latest consolidated definition status) with the P3e overlay:

* RECEIPTED 256; EQUALITY_PROVED 694; EQUALITY_DOMAIN 6 (the 4 loop-return refinements and the two domain-restricted transport definitions); CONDITIONAL_ON_BINDING 6; HAND_ADAPTED 33; NO_FROZEN_COUNTERPART 4; OPEN 708.
* OPEN splits into 325 with no overflow-correct fresh emission, 224 failed or other, 119 wrong-basis records (counted OPEN under the 2026-11-09 ruling), 40 with no record.
* Module rollups: 143 OPEN, 40 RECEIPTED, 16 EQUALITY_PROVED, 1 CONDITIONAL, 9 reach no annotated definition. Compared with the first run (PCXA_: 435 EQUALITY_PROVED, 915 OPEN, 247 wrong-basis), the gain comes from P1h (overflow-OFF equalities), P2g/P2h, P3b-d and P4e.

Ledger30 view (599 CLOSED rows): 138 clean at definition level, 447 conditional, 12 reach no emitted module, 2 rootless; 561 rows rely on a module whose rollup is OPEN (module-level, conservative). The 138 are clean only with respect to annotated definitions; unannotated hand-written names they reach have no provenance status, and the hand models in section 4 are a separate condition.

Receipted does not mean overflow-configuration checked: the receipt's configuration is not re-derived here.

## 2. Combined import

One root module, PRVCmb_ROOT, imports PRVH_WrapAdd and 13 bundle modules PRVCmb_C01..C13, which together contain the 200 credited files of PCXB_CREDITED_FILES.json (rule PCXB-C1: the proving file of an EQUALITY_PROVED, EQUALITY_DOMAIN or CONDITIONAL_ON_BINDING PCQH record; for the 93 records with no proving_file, the P2g final file declaring the theorem or the P4b/P4c final files; plus the generic lemma modules and PRVEq_transport_row_P3.lean). It is built on the ledger30 gate export with no gate rebuild, from cached bundle objects. The audit pass (PCXB_L019, exit 0, 33 s, peak 6.0 GiB, swap 0) covers 2779 constants under PRV*/PCVE*: all 2121 theorems were audited one by one and every one depends only on propext, Classical.choice and Quot.sound. All 766 credited theorem records are found by name in the audit.

Name collisions (576 names collided across the credited files) are resolved by a deterministic textual rule (PCXB_rename.py, PCXB-C2): in the j-th file of bundle k, PRVEq., PRVFresh_ and the helper namespaces PRVH, PRVC, PCVE are suffixed by the tag Ckk_Fjj. After the rule, no declared name collides. An outer wrapping namespace was tried first (PCXB_L004) and failed, because it hides gate names that the file resolves through its own namespace; that shape is retired. The rename changes theorem names only, not statements; it is a textual transformation checked by compilation, not by a statement comparison.

Excluded: 336 PRVEq files that prove only superseded, wrong-basis or OPEN records (PCXB_SUPERSEDED.json), and all scratch files with sorry (PRVC_N02_exp*, the PCVB_L025/L030/L031 probe copies, the P2h probe files). No credited file contains sorry, an axiom declaration or the text native_decide.

One finding. The union of axioms over all 2779 targets contains 16 axioms named _native.decide.ax_N. They belong to one Aeneas-generated fresh definition, r1_wire.Error.Insts.CoreFmtDebug.fmt, in the fresh text of the P4e PrefixAggregateParser file (the archive Funs; the gate deletes this Debug impl). No theorem depends on it (per-theorem results standard), but the credited file does carry a definition elaborated with native evaluation. It should be removed from the credited file or the file's fresh text edited; I did not edit it.

Scopes: 19 Lean scopes of the 20 budgeted, 0 extraction, 0 Kani, one at a time, 6G/8G caps, 180 s unraised. Failures: L002 (audit helper used a CollectAxioms API absent in this toolchain; rewritten) and L004 (wrapping shape). Longest wall 63.7 s, peak RSS 6.4 GiB (C09). The bundle sha256 values in the receipts match the files committed here.

## 3. Findings stated plainly

* transport.Variant.row_loop.body is a real body difference: the gate has checked shifts (j >>> i, i2 <<< i4), the overflow-OFF emission has wrapping shifts. The two bodies do differ on inputs above the bound. P3e (PCVE_L006) proves them equal for iter.end <= 16 (row_loop.body, row_loop: EQUALITY_DOMAIN with that domain) and row equal on all arguments (EQUALITY_PROVED). The bound 16 is a hand argument for sharpness, not machine-checked. These upgrades rest on the NPE_ ShrAmt check (evidence/shramt-20261110/NPE_SHRAMT_CHECK.md, on research): in the overflow-checks-off configuration ShrAmt is faithful to Rust's wrapping shift for every I32 and Usize amount, proved in Lean with standard axioms. Residuals: not checked against an SBF-target build (runtime tests were x86_64); it relies on Lean's usize width equalling the target's, which every gate module already shares; in checked mode it is not faithful for usize amounts >= 2^32 and must never be used there. 35 records that carried the bridge are marked (PCXB_SHRAMT_UPGRADED.json): the NFN fast_domain and for_range families including fibre_point, and the three transport definitions. The R22 split treats this body as a mixed configuration (checked shifts in the gate, wrapping in the emission).
* M31.mul source drift is closed by full equality (P3b on the AspisR72Sampler emission: both branches, all inputs). The older field.rs blob a47a9996aa63 (first commit 0319ac2b7b5) is recorded for AspisR72Sampler.
* S1 link and old cone: S1ValuesOwnedModelV1 is in the deployed_splitB cone (TAS_G0_AUDIT.json lead_provenance_check, via NOC_PrepareFront.values and LIBC_ExpandValuesModel.source); the old RPx_Deployed cone lacked it (PCWD_REACH.json). That is presence in the cone, not a review of what the link states; ExpandValuesFrozenEq is unproved and all 8 definitions of the module are OPEN.
* Cut-module equalities tie reproduced text to the gate, not archived crates to the frozen source.
* AspisR1CircleSampleWrapper is a flagged substitute (patched Aeneas not on the host; unpatched build used on the archived LLBC), not a reproduction.
* The gate's extraction feature set is inferred (PCQF-C3), not recorded.
* Toolchain labels: Charon driver nightly-2026-06-01 and RUSTUP_TOOLCHAIN nightly-2026-09-17 both appear; the tool and label are kept per definition where known. Emissions come from two Aeneas builds (959659a6 and aeneas-b59d5188-extended).
* R22 split (checked-to-wrapping belongs to R22, which cites frozen b2727acd, not 4bb3b3f; that pin is Stream A's): by body class the cone has 51 wrapping-configuration definitions (match the deployed ELF directly once equal), 217 checked, 8 checked with some wrapping, 1431 with no arithmetic. The classes come from a text detector.

## 4. Hand models, externals, non-frozen modules

PCXB_HAND_MODELS.json is the per-module inventory: 245 hand-written gate models in 56 modules (191 matched by a cone constant of the same short name, an over-approximation), plus named items: ShrAmt with the line "ShrAmt bridge: verified against Rust semantics and the pinned translation, NPE_ 2026-11-10 (overflow-checks-off only; never reuse for checked shifts with amounts wider than 32 bits)"; array_from_fn_copy standing in for the opaque core.array.from_fn with 23 blocked dependants (OPEN); compact.OFF_*; the Port3/Port4C/Port5Q2/AdapterRwModel parametric records (HAND_ADAPTED); and the cross-crate constant encoding assumption in one line (proved only for M31 and QM31 ZERO/ONE). PCXB_TRUST_PROPOSALS.md has proposed text only.

Of the 601 externals with no gate definition: (a) 502 resolve by a gate constant or hand model elsewhere (suffix match, over-approximate); (b) 0 are covered by a literally matching existing trust row (the appendix SDK rows are borrow fields, not Pubkey/Hash models); (c) at most 99 unresolved, an upper bound since gate sources were not exhaustively searched (PCXB_EXTERNALS_601.json).

The 26 non-frozen cone modules (PCXB_NONFROZEN.md): 2 ALL_DEFINITIONS_EQUALITY_PROVED (AdapterReconstruct Funs and Types), 1 OPEN, 23 UNVERIFIED (detector-blind). Definitions: 170 EQUALITY_PROVED, 150 OPEN, 11 HAND_ADAPTED, 4 EQUALITY_DOMAIN, 4 NO_FROZEN_COUNTERPART (eight gate-only helpers listed with reasons).

L187 reconciliation (PCXB_L187_RECONCILE.json), by source hash and declaration text, not object: of the 14 unrecovered modules, 12 emitted ones agree; of the 42 versioned, 10 emitted agree; of the 159 with no or several sources, 73 emitted agree; of the eight SOURCE_PATH_DIFFERS, four agree, two are not emitted modules, and AspisR1WideToBytesSource.Funs and ClaimsUnrolledParentTypes are switched to the recovered source (3 and 2 declarations differ from the old text; the credited equalities are against compiled constants and do not change). The 24 no-source modules all serve rows and stay unchosen (PCXB_OWNER_DECISIONS.md); the 26 second-tier modules are OPEN.

## 5. What is proved, conditional and open

Proved: the Lean equalities counted EQUALITY_PROVED and EQUALITY_DOMAIN above, with standard axioms, in one combined environment. Conditional: 6 definitions on constant bindings or parametric transports; the 256 RECEIPTED on their receipts; every statement on the hand models above and on the ShrAmt residuals; every checked-configuration definition on R22. Open: 708 cone definitions, 33 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, the 24 and 26 cut modules, 99 externals.

Target not yet established.
