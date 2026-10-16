# Actual eight-lane digest binding source proof

`AspisR1TerminalDigestBindingCandidate.R0PBridge.add_digest_binding_is_r0p` proves the actual isolated candidate binding wrapper succeeds, returns a canonical eight-cell array, and agrees in every cell with the existing R0P.digestAddBinding model. The source right-tweak branch performs actual M31 modular addition before lifting; its exact postprocessed target is preserved. Inputs are canonical accumulator, selector and openings, canonical expected M31 words, and the actual start-plus-eight bound. Arithmetic, reads, writes, checked index operations, loop execution and model equality are derived.

The source kit retains the exact loop, wrapper and tweak constant from sealed generated candidate Funs04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e. The checked manifest compares all three declaration bodies after only binding-name shortening and whitespace removal. The source declarations execute under an isolated namespace with the existing shared field/public carriers. The original field-only Funs object intentionally does not contain the whole terminal; no false equality to a missing original constant is claimed. Candidate-to-release caller/artifact correspondence remains separate.

The fuel invariant tracks completed lanes and untouched seed lanes. The wrapper starts at zero and completes all eight lanes. Its two axiom reports cover both the fuel theorem and the wrapper; the bridge has its own report. Existing exact field arithmetic, lift_m31 and range traversal proofs are reused.

An actual joint import check with ScalarSuffixPacking found duplicate declarations from compiling the same lift source under both top-level and dotted module names. Exact now imports the existing top-level TerminalLiftM31Exact. A fresh overlay rechecked Exact, LoopExact, Wrapper, R0PBridge and the joint import probe in dependency order; all passed. The original source-only check was under the undotted TerminalAddDigestBindingSource target. Its intended dotted consumer source has the identical source hash; consumer receipts retain their exact cached Source object pin. These focused records do not claim a final coherent release replay, which remains due when the whole caller closure is complete.

Every included check exited 0 under capped NUC scopes with zero process swaps. All theorem axiom reports contain only standard Lean axioms. Receipts record exact target, source revision, source/object/import hashes, commands, resource reservations, wall/RSS/swap and axiom reports. No broad replay was run. The public digest outer loop/wrapper, full terminal, admitted caller/transcript/custody, accepted-spend soundness and privacy remain open.

| Checked target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `TerminalAddDigestBindingSource` | 1.771 | 3987728 | 0 |
| `AspisR1TerminalDigestBindingCandidate.Exact` | 1.789 | 4000432 | 2 |
| `AspisR1TerminalDigestBindingCandidate.LoopExact` | 2.863 | 4008596 | 0 |
| `AspisR1TerminalDigestBindingCandidate.Wrapper` | 1.73 | 3987280 | 2 |
| `AspisR1TerminalDigestBindingCandidate.R0PBridge` | 1.73 | 3980460 | 1 |
| `SemanticScalarDigestJointImports` | 1.555 | 3972644 | 2 |
