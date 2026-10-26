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
