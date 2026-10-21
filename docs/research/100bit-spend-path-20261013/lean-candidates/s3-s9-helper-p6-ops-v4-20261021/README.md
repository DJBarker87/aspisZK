# S3/S9 range-fold P6 model

This packet contains a reviewed operational model of the generated `Iterator::fold.default` control flow. `rangeFoldRun_eq_foldIndices_of_trace` says that whenever the selected Aeneas `Range<usize>::next` model emits an ordered successful trace, folding the callback through that range is exactly the ordered `foldIndices` fold. The model carries callback state and propagates `Result` failure/divergence. It does not assert Rust `std` correspondence; that is a P6 boundary, checked here with a small optimized Rust differential test.

The Lean target is a generic model, not yet the `factored_s2_libra_weights` consumer. It does not prove source caller/result equivalence, helper field operations, or whole `Weights::pair` behavior. The current whole-pair source cut remains diagnostic: its six field-operation bodies are fail/panic stubs, and normalized Pair equivalence with the frozen method remains open.

The accepted Lean run used the recorded bounded NUC scope (High 1 GiB, Max 2 GiB, Swap 0). Its preflight labels the source revision as “working tree at launch”; no exact Git HEAD was captured, so the packet records that provenance gap instead of inferring one. No compiled Lean objects or binaries are included.

The differential test checks four ordered range elements against an explicit Rust loop. It supports the P6 model boundary only and is not a proof of the production helper.
