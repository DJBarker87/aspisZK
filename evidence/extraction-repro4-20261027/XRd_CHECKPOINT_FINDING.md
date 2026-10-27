# New required-body translator obstruction

The approved selector-only second release artifact is body-complete at the
LLBC layer. Pinned Aeneas c0cf4fcc… cannot produce the complete requested Lean
kit: XRd_002 fails in verifier::checkpoint with “Could not match the contexts”,
source verifier.rs:330:4–330:55 (the `for root in &p.roots` loop), compiler
interp/InterpJoin.ml:2209. Full source/target contexts and stack are retained
in XRd_002/stdout.log. This is not evidence of a shipped-source defect or a
counterexample to a mathematical projection statement.

XRd_002 exit2,20.970277s,246048KiB,swap0. XRd_003 changes the diagnostic mode
by removing abort-on-error to try to collect independent successes; the same
exception remains fatal, exit2,20.761485s,244288KiB,swap0. Neither writes any
Types/Funs. No timeout/memory kill; no cap change; no translator/library patch.
The original LLBC is not masked or otherwise rewritten.

XRd_004 is a selector-only independent subkit lowering which additionally
makes checkpoint opaque. It is explicitly INCOMPLETE and cannot discharge the
checkpoint binding. It preserves the complete 80465ea3… artifact and the
failed chain; it is not a replacement release-success claim. Aim: obtain
independent required bodies for typed association work.
