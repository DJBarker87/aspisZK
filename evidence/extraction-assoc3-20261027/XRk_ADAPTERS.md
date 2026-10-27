# XRk generated adapters (candidate; no P6 credit)

The authoritative raw Funs input is retained by XRj_L013 with SHA256
f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5.
XRk_transform.py is deterministic and performs no extraction. It records input
and output hashes and full before/after text for every changed declaration in
XRk_adapter_changes.json. The raw input is never edited.

Imports/namespace are isolated as XRk_ modules/XRk_Release. compact references
are fully qualified to avoid local value shadowing; declaration names remain.
The fixed-library trait signatures cannot be altered by defining externals:
Iterator.next requires a pair, and FnOnce/FnMut records have fixed return types.
Thus the following narrowly scoped generated-reference adapters are necessary:

* Mutable Iterator record next drops its restoration callback for the shared
  trait interface. Its step_by/enumerate fields use the pinned default methods
  with the required pair ABI. Explicit mutable callers retain callback models.
* Mutable DoubleEndedIterator record next_back projects its pair. Direct
  mutation/reverse operations retain explicit restoration.
* Enumerate mutable next and the mutable Rev next use XRk_enumerateNext and
  XRk_reverseNext. Their loops are unchanged; callbacks reconstruct mutable state.
* Array.into_iter uses XRk_intoIter: restoration applies to the captured initial
  iterator, then Array.from_slice restores the original array carrier.
* closure_1 FnOnce trait drops its returned capture; FnMut trait applies the
  emitted restoration to the returned capture. The emitted call_once/call_mut
  definitions themselves remain unchanged.
* The state-returning array::from_fn use in low_base_p_digits uses
  XRk_fromFnState, preserving the final closure state; plain uses stay plain.

These adapters are implementation models with OPEN P6/library-ABI association,
not new trust axioms. Every wrapper is transparent. No formatter axiom is added.
No modified generated declaration is imported by a security top. Any failing
Funs elaboration produces no accepted Funs object.

L034 identified two additional restoration-call sites: mutable rev_back in
closure_1 and enumerate_back in BatchedWeights.finish consume endomorphisms,
while the template externals consume states. XRk_revRestored and
XRk_enumerateRestored apply the endomorphism to the captured initial adapter
state before invoking the original backward projection. The corresponding
callee names alone change in the generated definitions. compact.check_values
and compact.expand_values resolve at _root_.compact (external definitions),
while compact types/constants/other generated functions resolve at
_root_.XRk_Release.compact. The transform distinguishes them explicitly.
All before/after declaration blocks and final hashes are regenerated together.
