# S4 Prepared.new mapped-body adapter (2026-10-22)

This focused Lean result maps CurrentCaller field carriers to the retained S1 `PreparedScratchModel` carriers. For one successful execution of that mapped source-shaped body, `prepareByS1Body_success_powers` derives, from the same run, the gamma used by the returned Prepared value, the `B.powers` call result, and the equality between mapped returned powers and the returned scratch. The child boundary bundle `B` remains explicit.

The source basis is the exact retained `Prepared::new` cut (verifier.rs lines 72–89 in the current frozen source, pinned in `dependency-pins/prepared-new-source.json`) and the accepted S1 substitution mapping. The exact current Prepared.new body and S1 model body are compatible under those named child substitutions and the fieldwise maps in the theorem.

This result does not install the mapped body into an arbitrary `Tx1OpsCut.Ops.prepare` field. That field accepts the full `public/proof/hash/observer` preparation operation; this mapped body begins after semantic/view inputs have been produced. The bridge from the actual caller's full prepare implementation to this child adapter, and concrete bindings for sampling/powers/cached-claim, remain open. It makes no production adoption or runtime-dispatch claim.

The v5 focused Lean 4.32 compile passed with standard axioms `[propext, Classical.choice, Quot.sound]`, 2.642s wall, 2,245,246,976 B aggregate RSS, and zero swaps. Attempts v1–v3 are retained as diagnostics; v4 was green before adding the axiom directive. No compiled object is included.
