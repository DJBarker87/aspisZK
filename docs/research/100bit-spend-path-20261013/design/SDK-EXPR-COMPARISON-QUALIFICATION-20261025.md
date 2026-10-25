# SDK comparison qualification: alpha helper versus literal expressions

Correction: the reused Port18 sameDeclaration helper's Expr fields are compared by derived BEq Expr, which is Expr.eqv. This is alpha equivalence and ignores binder names/annotations. Prior helper-based results labelled strict ConstantInfo matching, strictly identical duplicate declarations or strictly identical complete public types establish ONLY the recorded full non-Expr metadata comparisons plus that expression equivalence. They did NOT establish binder/annotation-sensitive literal expression equality. This qualifies owner reports and immutable release metadata/READMEs with those descriptions; old receipts/data are preserved, not rewritten.

The limitation is independently visible in pinned Lean4.32 Expr.lean: BEq Expr delegates to Expr.eqv; Expr.equal explicitly includes binder names and annotations. Exact source and Declaration.lean snapshots/pins are retained in evidence/s126-current-caller-20261021/sdk-literal-comparison-20261025. The lead correction is recorded at bc8b650518. No source/security theorem or deployment closure had been claimed from data comparisons.

Separate evidence remains valid at its stated scope: complete source byte equality, preserved raw ConstantInfo type/value/group/recursor data and artifact hashes, ordinary kernel-checked theorem/equality results and their standard axiom audits. The original SDK full-function equality proved by normal elaboration/kernel checking is not replaced by this metadata comparator and is not withdrawn. This qualification does not prove native execution, totality or release binding either.

New S126SdkLiteralComparisonV1 preserves the entire legacy metadata helper, then additionally requires Expr.equal on complete type, full value including opaque/theorem values, and every recursor rule RHS. Rules/order/count/constructor metadata, definition hints/safety/mutual groups and every prior non-Expr field check remain. No alpha normalization, binder erasure, expression rewriting, declaration insertion or trust import occurs. Synthetic DATA counterexamples verify rejection of binder-name/annotation, opaque-value and recursor-RHS changes and of metadata safety changes; no synthetic object is inserted into an environment or used as a theorem.

The focused current-data audit checks ONLY this owner's complete three-layer CURRENT data, the owned original/factored comparisons already made, and both same-source proof refresh TYPE comparisons. It does not duplicate the lead's original ROOT/current 1059-pair or missing-body/kernel job. New results are recorded separately and must be read before any literal selection claim. Historical old fields named identical/same_type retain their original alpha-helper interpretation even if a new stronger check succeeds.

The smallest new comparator target is checked first, then its dependent data reader. No unchanged proof, verifier, runtime, source export or full manifest replay is requested or performed. No production/toolchain/namespace/source decision follows from a binder-sensitive data comparison. Kernel reconstruction and all actual native/source/artifact obligations remain open.

## New binder-sensitive results

Read-only companion: `/private/tmp/s126-sdk-literal-comparison-release-20261025-v1`, manifest `ef66913f1470c05e16f3e5573378d8883ea9a42e687611c5e7e4c4cb73ccec27`. This contains audit source/results/pins/receipts, not replacement raw constants or a new trusted environment. The three earlier immutable raw releases and historical receipts remain unchanged.

- CURRENT: all43 duplicate comparisons on the28,518-constant/1432-fragment union pass COMPLETE legacy metadata plus Expr.equal type/value/opaque/recursor-RHS guards. Literal duplicate coalescing is now checked for THIS exact current dataset.
- Proof refreshes: all6 old/new public types are Expr.equal; both versions are theorem declarations. The new proof bodies remain explicitly selected/reviewable, not silently original historical objects.
- Owned original/factored scope:236 paired declarations;233 match the old alpha+metadata helper, only182 are fully literal. All236 types are alpha equal, only212 are literal. There are54 nonliteral declarations, including51 that old helper accepted;24 paired types differ syntactically. Three new auxiliaries remain unmatched. ALL names/flags are retained in results.json, including exact nonliteral/type lists.
- Entry, Record, Allocator, Account, FirstCut and SecondCut INDUCTIVE declaration records themselves pass the new literal guard. This is not an assertion that all their generated projections/matchers/injectivity/size functions or proof values are literal; the24 type/54 declaration differences remain explicit.

The whole-factor literal-identity selection flag is FALSE. No differing declaration is first-wins selected as literally identical. Alpha-only comparisons are not kernel/source equivalences by this audit; actual computational/source/caller joins must use the ordinary kernel-checked results or an explicit reviewed reconstruction/transport, with the enclosing original ROOT/current/ALL14/native/event/source/artifact work remaining lead-owned. Existing first_eq_original is separately kernel-checked and not withdrawn; this audit does not extend it to all54 differing declarations. No native/release/security premise is claimed discharged by these data checks.

The comparator checks every expression-bearing ConstantInfo field: full type, full definition/theorem/opaque value (allowOpaque=true), and each ordered recursor rule RHS. The legacy helper retains all current ConstantInfo non-expression fields, including hints/safety/constructor/rule/group metadata; pinned Declaration.lean allows that coverage to be inspected. No expression normalization/alpha conversion or declaration insertion occurs.

## Focused validation and failed preflight

Smallest comparator first: sdk-literal-comparator-v2 exit0,4.164952083025128s,RSS1284636672B,swap0. Dependent sdk-literal-data-audit-v1 exit0,9.428882000036538s,RSS1462910976B,swap0. Both use atomic local lock,-j1,-M4400,warm caches. Axiom result N/A: these are IO/data audits, not logical theorem proofs. Synthetic fixtures reject the known binder-name/annotation, opaque-value and recursor-RHS counterexamples while retaining metadata/reflexivity checks; data only, never environment declarations.

Initial comparator-v1 failed local record-layout syntax and ordinary #eval refused the error-recovery term; it is retained/excluded. No #eval! override, axiom, trusted import, proof/whole-package/native/runtime replay or host process ran. Preparation-v1 used the wrong historical JSON key(inputs vsfiles) and failed BEFORE compiler launch; exact source/failure record retained, corrected preparation checks every historical source/object hash. All selected inputs/transports matched post-audit.

Source-only focused-extractor-proof-packet-v1 metadata, exact source/tool/API/import/object pins, target/status/wall/RSS/swap and full logs are under evidence/s126-current-caller-20261021/sdk-literal-comparison-20261025 and per-attempt receipts. No binaries distributed in Git. New metadata audit:

```
python3 tools/s126-sdk-literal-audit-20261025/check.py
python3 tools/s126-sdk-literal-audit-20261025/check.py --released
```

This responds to lead bc8b650518's comparison correction at the OWNER data scope only. It does not spend or duplicate the lead's bounded1059-pair original ROOT/current diagnostic. Native initializedness/allocation/drop/full-loop/Terminal/domain and original/current/kernel/event/artifact joins remain open; <=2^-100 per-attempt soundness is not established.
