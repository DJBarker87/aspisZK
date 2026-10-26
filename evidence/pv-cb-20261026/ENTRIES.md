# Callback work, first checkpoint

Branch codex/pv-cb-20261026; base 821157fbdd16034290613b9c4feac7023e15498c.
Target not yet established. **No ledger row or endpoint premise is claimed removed.**
The checked installation equations below are source/value interpretations; native
source correspondence must be audited before promoting these to full row closure.

| op | row | disposition at checkpoint | theorem / receipt |
|---:|---|---|---|
|3|V169|checked source/value installation; native audit pending|PV_CB_Take.op3_installed; 22801.json|
|25|V177|checked Unix byte-borrow installation; native audit pending|PV_CB_PathBorrow.op25_bytes; 22803.json|
|26|V178|DEFERRED to pv-runjoin3 for full allocator-effect law|Path::join clones/extends an owned buffer; allocation/abort outcomes depend on native allocator state absent from the Vec value carrier. No unconditional successful native equation supplied.|
|28|V179|checked bounded carrier interpretation; full row OPEN|PV_CB_StringPath.op28_bytes; 22804.json; explicit length premise, invalid-carrier panic branch is an interpretation, not extracted shipped code|
|29|V180|checked Unix byte-borrow installation; native audit pending|PV_CB_PathAsRef.op29_eq_deref; 22805.json|

Initial checks for ops3,25,26,28,29 were performed directly with the required
`git log -1 --format=%H` command and `git show` table searches. rw head was
821157fbdd16034290613b9c4feac7023e15498c; dict head was
4b53f2d33d28dcf0ac25c87eb0cddedfe8f8c059. All five table rows were OPEN.
The required multi-revision log command prints only the newest commit across
both histories; subsequent machine receipts also record each branch separately.

Read-only sibling dependency: R1Z.PDict_PathTypesSource from dict head above.
Existing ProverRw modules are imported read-only. No shipped Rust, artifact,
observer, simulator, root theorem, shared source or existing object was edited.
New PV_CB objects only. Failed attempts22800 and22802 are retained; fixes were
respectively a nonexistent simp lemma and explicit native-carrier instance scope.
All successful theorem audits use only propext, Classical.choice, Quot.sound.
The receipt collector fingerprints direct import objects after the focused run;
this is not a coherent dependency-closure replay. Ledger before/after:0 removed.

## Second checkpoint (source preparation during admission hold)

| op | row | disposition at checkpoint | theorem / receipt |
|---:|---|---|---|
|30|V181|OPEN: owned-reference gate pending; allocation alone is not treated as sufficient reason to defer value work|String::with_capacity; current carrier omits capacity; retain capacity-overflow/native allocation outcomes|
|31|V182|OPEN: owned-reference gate pending|String::push_str; UTF-8 concatenation plus capacity/overflow behavior must be preserved|
|32|V183|OPEN: native allocation-result gate pending|Vec::try_reserve_exact; do not replace allocation error with unconditional success|
|33|V184|statement prepared, NOT CHECKED; native gate pending|PV_CB_Pop.op33_installed; safe borrowed-slice reference prepared|

Before each of these ops the sibling heads/tables were recorded in
opN-sibling-check.json. No sibling installation found. No row removed.
First native gate remains unstarted: initial admission and two retries denied
on aggregate reservation. Three-minute intervals respected; caps not bypassed.
The owned reference is cfg(kani)-only and no shipped crate was changed.

## Third checkpoint

| op | row | disposition at checkpoint | theorem / receipt |
|---:|---|---|---|
|34|V185|source statement prepared, NOT CHECKED|PV_CB_IsEmpty.op34_installed|
|35|V186|source statement prepared, NOT CHECKED|PV_CB_VecDefault.op35_installed|
|36|V187|source statements prepared, NOT CHECKED|PV_CB_VecArray.op36_accept/op36_reject|
|51|V195|SKIPPED(sibling source installation), reuse being composed|ProverRwP6FlatInstall.source; sibling14008/14009, success-p6/final-state.json|

op51 remains OPEN in the dictionary table, but the read-only prover sibling's
source installation is already checked at14009 and its source at14008. This
is recorded as source-level reuse, not a claim that native composition or the
headline premise was discharged. New Codecs composition is not yet checked.

Kani1/20: checks::take_u64 and checks::take_nonzero both pass, no stubs;
see kani-take-001/receipt.json. Generic reference extraction next. This gate
does not establish arbitrary Default/Drop native behavior. Lean6/100,4 green.

## Relaunch 1, checked vector and codec checkpoint

Prior budget: Lean6/100 (four green), Kani1/20. Focused attempts22806–22811
are green; all printed axioms are standard. Initial direct execution of the
non-executable shared launcher returned126 before any Lean attempt; invoking
it with `sh` used the existing launcher unchanged. No reservation was bypassed.

|op|row|status|theorem / receipt|
|---:|---|---|---|
|33|V184|INSTALLED (value; native gate pending)|PV_CB_Pop.op33_installed, op33_empty;22806.json|
|34|V185|INSTALLED (value; native gate pending)|PV_CB_IsEmpty.op34_installed;22807.json|
|35|V186|INSTALLED (value; native gate pending)|PV_CB_VecDefault.op35_installed;22808.json|
|36|V187|INSTALLED (value; native gate pending)|PV_CB_VecArray.op36_accept/op36_reject;22809.json|
|71|V197|INSTALLED (emitted source)|PV_CB_Codecs.op71_installed;22810.json|
|72|V198|INSTALLED (emitted source)|PV_CB_Codecs.op72_installed;22810.json|
|77|V199|INSTALLED (callback order)|PV_CB_PointClone.op77_installed;22811.json|

Row numbers checked against research:evidence/privacy-recount-20261026/ROWS.md;
row-map.json retains the exact op-to-row map.
No endpoint premise or ledger row removed (before0/after0 removals). Native
allocator/Drop/side-channel obligations remain separate from value equations.

## Checked Phi and Merkle values

|op|row|status|theorem / receipt|
|---:|---|---|---|
|80|V202|INSTALLED (emitted source)|PV_CB_Phi.op80_installed;22812.json|
|82|V204|INSTALLED (source constant)|PV_CB_Merkle.op82_installed;22813.json|
|83|V205|INSTALLED (source constant)|PV_CB_Merkle.op83_installed;22813.json|
|84|V206|INSTALLED (hash callback framing)|PV_CB_Merkle.op84_installed;22813.json|
|86|V208|INSTALLED (source constant)|PV_CB_Merkle.op86_installed;22813.json|

Standard axioms only; no endpoint premise removal or native effect claim.

## Checked field callback values

|op|row|status|theorem / receipt|
|---:|---|---|---|
|100|V209|INSTALLED (native-port source)|PV_CB_Field.op100_installed;22814.json|
|101|V210|INSTALLED (source)|PV_CB_Field.op101_installed;22814.json|
|105|V211|INSTALLED (source)|PV_CB_Field.op105_installed;22814.json|
|107|V212|INSTALLED (source)|PV_CB_Field.op107_installed;22814.json|
|109|V213|INSTALLED (native-port source)|PV_CB_Field.op109_installed;22814.json|

Standard axioms only; full selected caller/endpoint composition remains open.

## Checked context and statement-point values

|op|row|status|theorem / receipt|
|---:|---|---|---|
|110|V214|INSTALLED (source)|PV_CB_State.op110_installed;22815.json|
|111|V215|INSTALLED (source constant)|PV_CB_State.op111_installed;22815.json|
|114|V216|INSTALLED (context equality)|PV_CB_State.op114_installed;22815.json|
|118|V218|INSTALLED (emitted source)|PV_CB_State.op118_installed;22815.json|

Standard axioms only; no selected-native-caller or headline premise removed.

## Checked Zeroizing value projections

|op|row|status|theorem / receipt|
|---:|---|---|---|
|127|V223|INSTALLED (value)|PV_CB_Borrow.op127_installed;22816.json|
|128|V224|INSTALLED (value)|PV_CB_Borrow.op128_installed;22816.json|
|130|V226|INSTALLED (forwards zeroize callback)|PV_CB_Borrow.op130_installed;22816.json|
|131|V227|INSTALLED (forwards AsRef callback)|PV_CB_Borrow.op131_installed;22816.json|

Physical volatile erasure, fences, cleanup/Drop association and side channels
are not supplied by value equations. Their native effect adequacy is DEFERRED
to pv-runjoin3; these rows remain OPEN as complete deployment obligations.

## Take extraction and heap checkpoint

|op|row|status|theorem / receipt|
|---:|---|---|---|
|3|V169|INSTALLED (generic extracted reference; two native Default instances)|PV_CB_TakeExtraction.reference_eq/installed_reference/fail_preserved/div_preserved;22817–22819; kani-take-001|
|25|V177|INSTALLED (Unix byte value, length≤16 native gate)|PV_CB_PathBorrow.op25_bytes;22803; kani-pathbuf-002|
|29|V180|INSTALLED (Unix byte value, length≤16 native gate)|PV_CB_PathAsRef.op29_eq_deref;22805; kani-pathbuf-002|
|81|V203|INSTALLED (emitted source with allocator retained)|PV_CB_Heap.op81_source/op32_preserved;22820|

Take Types is empty; its import is folded into the generated Funs Aeneas import.
PV_CB_TakeRef.lean otherwise retains the generated function body and options.
22818 failed on simp lemma selection;22819 uses explicit reduction after the
callback equation and passes. The failed audit's sorryAx is not accepted.
Charon take and Aeneas take both exit0; aeneas translation was admitted after
the retained earlier barrier denial. Generic Default/Drop effects and unbounded
native carrier transport remain OPEN. Source/value installations do not remove
root premises. Budget now Lean21/100 (18 green), Kani2/20 (both green);
kani-string-003 was refused at its in-scope barrier, so has not charged a run.

## Vector composition and symbolic behavior

|op|row|status|theorem / receipt|
|---:|---|---|---|
|3|V169|INSTALLED value callback is independent of original field|PV_CB_Independent.take;22827|
|33|V184|INSTALLED with symbolic pop length/empty laws|PV_CB_VectorLaws.pop_length/pop_none;22824; PV_CB_Independent.pop;22827|
|34|V185|INSTALLED with symbolic nonempty law|PV_CB_VectorLaws.nonempty;22824; PV_CB_Independent.empty;22827|
|35|V186|INSTALLED default/empty composition|PV_CB_VectorLaws.default_empty;22824; PV_CB_Independent.default_vec;22827|
|36|V187|INSTALLED; original field eliminated from selected result|PV_CB_Independent.array;22827|

Composition selector is PV_CB_Composition.selected, checked22821. It only
composes source/value entries; whole-source caller and endpoint still open.
22823 failed on an explicit argument to an implicit List lemma;22824 fixes it.
22825 failed because polymorphic function equalities lacked type arguments;
22827 states pointwise equations, avoiding whole-dictionary elaboration.
Neither failed audit is accepted. All final printed axioms are standard.

22826 was refused by the unchanged-source guard (exit67), before Lean ran.
The intended edit had failed locally with a Python syntax error; corrected
source is sent as22827. No guard or launcher changed; refusal counts zero Lean.

## Composed codec/clone laws

|op|row|status|theorem / receipt|
|---:|---|---|---|
|51|V195|SKIPPED(sibling source); preserved in union|PV_CB_CodecComposition.wide;22828|
|71|V197|INSTALLED source preserved in union|PV_CB_CodecComposition.parse;22828|
|72|V198|INSTALLED source preserved in union|PV_CB_CodecComposition.write;22828|
|77|V199|INSTALLED ordered clone; first failure preserved|PV_CB_CodecComposition.clone/clone_fail_first;22828|

All audits standard; full ledger rows/endpoint removed remains0.
