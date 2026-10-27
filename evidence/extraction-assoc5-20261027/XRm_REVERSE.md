# Reverse adapter call-site result

L024 checks XRm_ReverseSites. There is one executable XRk_reverseNext site in
XRk_adapter_changes.json: sampler.low_base_p_digits.closure_1 FnMut's loop body.
XRk_revRestored occurs in its caller; XRk_nextBackPair is the double-ended
iterator dictionary entry, not an additional emitted executable call site.
The exact before/after declarations and source hashes are in XRm_reverse_sites.json.

caller_prefix proves the actual Array.to_slice_mut / Slice.iter_mut / rev prefix
constructs the cursor-zero initial state, for every capture. Reached describes
finite prefixes of the SAME emitted body with actual successful .cont
transitions. body_cursor proves each transition preserves cursor; cursor_zero
therefore proves the precondition at EVERY reached body invocation, including
the terminal invocation. reverse_site gives full Result/iterator/restoration
function equality with the cursor-respecting originalReverseNext at each call.
No successful whole-loop run is an extra hypothesis. nonvacuity constructs the
initial prefix for every capture. All new theorems have standard-only axioms.

Universal reverse equality remains false (XRl counterexample retained). This
site restriction does not establish native P6 for the surrounding library,
other dropped callbacks, extraction, whole sampler semantics or the actual top.
No adapted/source/shipped file was changed. Actual-top ledger delta is zero.
