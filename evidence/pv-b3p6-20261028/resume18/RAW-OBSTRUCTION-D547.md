# Raw release-wrapping obstruction and replacement shape (D547)

No raw local-body association is credited. No shipped-source counterexample is claimed.

K79104-r2 has the intended XOR assertion failure plus three checked-MIR subtraction failures. K79105 has only those three subtraction failures, not an output-equality failure. Cargo profile overflow-checks=false did not remove Kani's forced checked MIR. K79106 changes the actual compiler input to explicit RUSTFLAGS overflow-checks=off; pinned Kani rejects compilation with "Kani requires overflow checks in order to provide a sound analysis." It has no verification verdict. The guard prevented K79107; that unlaunched paired preparation is retired. Never retry this rejected configuration, modify the pinned tool, or credit it. K79100/01 remain historical failed/no-credit results.

The source is ordinary release wrapping subtraction on the full raw u32 domain. A canonical-only historical gate cannot supply the total raw Link without a separately discharged actual-caller domain law. Keep both obligations distinct.

Next total structural/Lean shape, with unchanged limits and no large whole-body reduction:

1. Prove a small monadic four-element from_fn/map construction law, recording the exact from_fn/try_from_fn_erased/Guard source chain already captured in ARRAY-INTERFACE-D543. Instantiate only fixed four-element arrays and pure callbacks; preserve cursor-before-call and initialization/restoration.
2. Interpret the four extension_limbs calls, then the sixteen raw_limb227 calls in output-major, limb-minor order. Bind raw_limb227 to the deployed closure's exact match cases0..3. Prove one named row theorem per output; keep arithmetic and source helpers locally irreducible. Do not unfold a 300-bind whole reference body in one attempt.
3. Retain release wrapping operations in every packing expression. Isolate the final four packing outputs into small modules. The source's all_local_limbs_bounded checks are pure total comparisons; release debug_assert is absent. If eliminating their dead accumulator, prove the ignored-result continuation law, rather than silently removing an effectful operation.
4. Compose the named prefix, four rows and four pack laws with N79161's exact reference provenance and a complete Result equality. No arithmetic reassociation or field-canonicality premise is needed for equality of the identical wrapping expressions. Apply whole-source structural map and carrier/array wrapper checks only after those focused proofs pass.

The independent alternative is to discharge every actual raw caller's canonicality, using the historical static-free canonical gate with its own matched control and std dossier. Do not narrow the total Link silently. Native compiler/copy/FnMut/intrinsic preservation remains V370; no new T item is available.
