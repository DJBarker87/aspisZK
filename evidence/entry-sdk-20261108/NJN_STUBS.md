# NJN stub register

No multiplication, digest value or PDA address-value stub is used. No
RuntimeCpiReadonlyEntry7, writable static, Option<fn> or function-pointer verdict
is used. No stub_verified call is relied upon for a Ref/RefMut/Result carrier.

The only native replacement is the EXACT canonical
core::ptr::copy_nonoverlapping → KMX_copy_nonoverlapping from
 evidence/kani-mitig-20261028/KMX_copy_stubs.patch (hash in NJN_KMX_PIN.json).
NIJ_gate checks KMX_stubs.rs, KMX_native.rs and KMX_CopyMeaning.lean against the
canonical source hashes before every native run, in addition to the frozen
lock/dependency graph and deployed resolved feature graph. Each lock is checked
again after Kani. Copy-dependent results require a matching semantic failing
control in the same configuration; timeouts and compiler/gate errors give none.

NJN_GuardModel.copy_range and its frame/drop laws consume the canonical
KMX_CopyMeaning.loop_spec/copy_frame induction, not a worker-authored copy stub.
This does not establish allocation/provenance/guard domains of actual stage1.

Pending SDK stubs: no logging stub is installed for borrow/deref/drop, Clock or
PDA because their complete paired law is not certified. Their candidate exact
statements and domains appear in NJN_LAWS.md. No caller-domain strengthening is
hidden by these candidate specifications.
