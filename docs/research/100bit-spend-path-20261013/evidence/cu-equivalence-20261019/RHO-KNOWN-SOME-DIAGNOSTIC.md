# Known-Some call-context source preflight

This is a rejected source-extraction diagnostic, not a candidate proof. Lean
was not launched because the MIR shape gate did not pass.

A new extraction-only root calls the exact existing new coefficient helper
with Some(pending), as the transaction callers do. The existing optimized-MIR
input is retained; only the helper's declaration gains inline(always), while
both full old/new coefficient bodies remain byte-identical. Existing noinline
opaque stubs prevent the optimizer from substituting their fake bodies. No
production Rust or compiler code changes.

This tests a distinct structural condition from the prior unknown-Option
root: the pending discriminant is known at the call site. The single 45-second
bounded extraction completed in 0.401 seconds, peak RSS 213164 KiB, zero process
swaps. Exact command/revision/features and source pins are in
rho-known-some-charon-a/receipt.json and the input kit.

The authoritative emitted call graph still has known_some directly call
rho_new::coefficients, and the generic Option.as_deref_mut is reachable.
The inline(always) attribute is present, but the requested specialization did
not occur. rho-known-some-shape.json records that graph gate and the LLBC hash.
No Aeneas or Lean result is claimed, no binaries are committed, and no further
inline-flag guesses are justified by this result.
