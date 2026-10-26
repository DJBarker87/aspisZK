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
