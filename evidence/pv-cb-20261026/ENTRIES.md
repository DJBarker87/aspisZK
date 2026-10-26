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

## Current wrapping arithmetic for op117 (helper stage)

PV_CB_CurrentComplex (22830) checks add/sub/mul against the retained release
carriers. PV_CB_CurrentComplexMore (22833) adds square/scale/double.
PV_CB_CurrentNeg (22835) proves branchless native negation = retained release
negation for every u32, using symbolic all-ones/zero masking.
PV_CB_CurrentQuartic (22836) checks add/mul/square/scale and the tower-r map.
All final axioms are standard.22831/22832/22834 failures are retained; no cap
or recursion setting was raised. The square recursion-depth failure was
replaced with explicit rewrites of both field constants, not a larger limit.

PV_CB_MaskSource (22829) is a PREPARED control rebind, not an installed
op117 source law. mask-rebind.json pins every retained control body; only
field method/type references are rebound. A fresh current-source extraction
comparison is still required. No closure is inferred from it compiling.

Native admission: the encoder Rust extraction passed after the proof manifest
removed its unused statement dependency (the first compile lacked a cfg(kani)
statement test support file). Translation remains unstarted after reservation
denials, including six retries. Some outer admission scans were earlier than
three minutes; they were denied and launched no work. A timestamp guard is now
used before retries. The only successful translation launch after a wait was
the earlier take translation. No reservation or launcher guard was bypassed.
Current Kani use remains2/20. Source snapshot is isolated in the assigned host
directory; shipped crates/programs and all sibling worktrees remain unchanged.

## Native std gates and finite mask controls

Kani3/20 (`string_path16`) timed out after180 seconds. The 16-byte arbitrary
UTF-8 scope remains open; it is not rerun unchanged. Prepared replacements
separate ASCII strings from single Unicode scalars. The timeout scope was
checked after completion: its cgroup was gone and no own child survived.
Kani4/20 (`path_join8`) passed, no stubs: every Unix byte prefix and suffix
with lengths0–8; source reference preserves absolute suffix replacement and
separator insertion. This is a bounded native value law, not an allocator
or whole-world proof. Receipt: kani-join-004/collected-receipt.json.

Encoder translation did launch after admission retry8; exit2 is Aeneas
`Not_found` in InterpReduceCollapse/collapse_ctx_following_sequence while
joining a loop. Its full trace and exact inputs are retained. No tool or
launcher repair is attempted; an owned index-based reference is prepared.

Mask preparation: PV_CB_CurrentTotal (22839) and PV_CB_PreparedTotal (22840)
prove machine-field and prepared-multiplier totality without success premises.
PV_CB_MaskLeaves (22842) proves the prepared power/tower leaves total.
PV_CB_MaskLinearsFinite.source (22847) relates the reverse linear loop to a
symbolic finite recurrence. Failed22837/38/41/43–46 are retained; no failure
is accepted. Current source audit is still required before op117 installation.

## Finite mask checkpoint

PV_CB_MaskLinearsTotal (22848) proves both finite-loop totality and the
complete two-linear-form result for all ten QM31 inputs. PV_CB_MaskIndices
(22850) proves coordinate masking gives0–3 and every literal factor exponent
lies below27, then transports these bounds through symbolic array reads.
Only tiny numeral inequalities are decided; no concrete field recurrence
or large domain is reduced. All accepted audits use standard axioms.

Direct current-mask Charon extraction succeeds, but Aeneas translation exits2
with the same loop-join `Not_found`; both receipts are retained. No op117
installation is claimed. Owned reference source is cfg(kani)-only, changes
iteration/storage shape while preserving call order, and still needs native
Kani correspondence plus extraction/control transport. The candidate's shipped
Rust, verifier artifacts, observer, simulator and headline are unchanged.

## Recursive encoder reference and checked cells

The bounded recursive encoder reference extracts/translates successfully
(charon-owned-encoder-002; aeneas-owned-encoder-002). The original loop-based
reference failure is retained byte-for-byte by its recorded hash.
PV_CB_OwnedEncoder compiles22854. Its raw Types/Funs and structural carrier
comparison are in owned-encoder-rec-generated/. PV_CB_EncoderInstall(22855)
installs this owned reference and removes the original op79 field from that
selected result, **but native correspondence is pending; full op79 stays OPEN**.

PV_CB_EncoderCell(22857) and PV_CB_EncoderFill(22859) prove bounds and the fill
recurrence, with an explicit primitive-multiplication-total premise. That
premise is not claimed discharged for every generic CodeField.
PV_CB_MaskCell(22860) proves both fixed coefficient-cell families total from
the checked literal exponent and tower-index bounds.

Kani remains4/20 until ASCII gate005 actually runs. Four further native
admission scans are retained; these refusals do not charge Kani runs.
Native collectors record post-run object/input snapshots. For changed proof
inputs, use the explicit retained per-run source snapshot; do not attribute
a current file hash to an earlier execution. No coherent release replay or
artifact equality is claimed by the focused checks.

## Symbolic encoder and mask totality checkpoint

Lean79/100 actual attempts through22879, excluding refused22826; Kani10/20.
MaskFillBody/Loop/Total, ForwardTotal, MaskHorner/Total and MaskTotal pass
22865–22872 (22871 failure retained). These establish PREPARED control totality,
not current mask extraction equality. EncoderRound/Basis/FoldBounds/Fold/FoldTotal/
EncoderTotal pass22873–22879 (22876 redundant simp failure retained, fixed22877).
Encoder totality retains explicit generic ZERO/ONE/mul/add/sub total premises.
All successful audits use standard axioms; no concrete512 recurrence is reduced.

|op|row|bounded native evidence; full status remains OPEN|receipt|
|---:|---|---|---|
|28|V179|ASCII0–8 and single Unicode scalar path value laws pass|kani-ascii-005; kani-scalar-006|
|30|V181|capacity0–16 empty/capacity lower bound passes|kani-capacity-007|
|31|V182|ASCII prefix/suffix0–8 push timed out180s; no unchanged rerun|kani-push-008|
|32|V183|usizeMAX byte reservation error and small0–16 content preservation pass|kani-reserve-overflow-009; kani-reserve-small-010|

Native gates use optimized proof profile, no stubs, capped6G/8G/swap0/Tasks64.
The original arbitrary UTF8 gate timeout remains. Row26's initial blanket
allocator deferral is superseded: bounded path_join8 passed; full generic law
remains OPEN. No ledger or endpoint premise removed: assigned73 before/73 after.
Fresh sibling checks79/117 at rwbbcc13a0 anddict1f5f2545 found no installation.

## Owned mask source checkpoint

Charon/Aeneas recursive mask extraction passes. owned_mask_source.py --check
matches all31 emitted field definitions to the checked current field source,
after the documented two signed shift-count API literals; carriers match
field-for-field and control bodies are otherwise unchanged. PV_CB_OwnedMask
22880 compiles. Tower source/totality22882 and wrapping predecessor22883 pass.
Owned linears/horner finite correspondence22884/85 and totality22886/87 pass.
Failed22881 retained (wrapping predecessor missing);22888 linears root bridge
fails on iterator default reduction and is being corrected. Standard axioms
on all green theorems. Native row117 stays OPEN: Kani12 unwind32 failed in
37-element Arbitrary initialization; corrected40 run13 timed out180s. No own
solver survived. This is not a counterexample and not native correspondence.

Late source audit checks205–261 in ascending order before source inspection;
per-op sibling receipts and exact emitted function names are retained.
Existing sibling source installs246/249/250 are reused, alongside225/254.
Native effect deferrals:232 returns measured Instant timings (z4/z9e.rs196–220),
257 invokes native worker scheduling plus optional trace mutex (host_work.rs),
261 writes std filesystem state. See late-op-source-inventory.json. Other
unfinished pure rows remain OPEN; no arbitrary effect deferrals are invented.
