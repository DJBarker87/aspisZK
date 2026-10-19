# Candidate 12: complete initializer outcome

Candidate 12 remains open. This checkpoint closes the initializer's matching-length premise without assuming allocator success.

`CuSavingsRhoHeap.initializer_outcome` consumes the entire emitted `heap::filled` helper and the complete constructor wrapper. Its reserve operation and error type are universally parameterized. Every successful helper return passes through the original runtime `Vec.resize`; therefore its length is correct regardless of the vector returned by reservation. The constructor then overwrites every row through the original mutable iterator/Zip handbacks. Allocation errors, runtime failures and divergence remain in the outcome equation.

The original mutable zip frontend emission failed. The supported binding is explicit: an exact for-block was lifted into a helper, inverse inlining recovers the original Rust constructor bytes, the resulting complete wrapper was emitted, and the helper is interpreted through the existing reference runtime definitions. `sourceFor_eq` and `source_eq` prove those substitutions. The audit compares the full wrapper body, not a selected success branch. Generated function bodies remain unchanged; nominal carriers and unused colliding discriminator registrations are documented in the promotion manifests.

`CuSavingsRhoAllocationBound` separately proves symbolic integer bounds for the pinned SDK bump allocator: at most 8199 extra bytes for 256 raw rows, or 2055 for S2's 64. This does not yet bind `try_reserve_exact` to that allocator or establish the callers' future heap budget. Those resource obligations remain open.

Run `python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-rho-initializer.py` for source normalization, current source/receipt identity, original cache coherence, dependency-object identity and axioms checks. `RHO-INITIALIZER.json` enumerates focused commands, source revisions, features, exits, wall times, peak RSS and swap. Accepted declarations use only propext, Classical.choice and Quot.sound. The first alignment attempt used native bv_decide axioms; it is explicitly rejected and replaced by a symbolic proof.

Remaining: source reserve/resource binding; actual accumulation traversal and actual caller invariants; tx1_finish, tx2 and tx2_authenticated outcome/checkpoint/cryptographic-call/effect composition. No production Rust changed and no CU/runtime replay was repeated for these proof-only edits.
