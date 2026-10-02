# R327 source-body and dependency audit

This is a read-only census of the saved R327 LLBC versus R297. The builder verifies both input hashes, resolves Charon's inline `HashConsedValue`/`Deduplicated` records, compares declaration metadata and signatures, and records a compact direct-call census. It does not invoke Charon, Aeneas, Lean, or a proof tool.

R327 succeeded as an extraction: Charon exit 0, `has_errors=false`, LLBC SHA `9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442`. It retained the local batch root and its body. The embedded root source text is byte-identical to R297's source copy, and the decoded root body is equal after ignoring only statement IDs. The direct root call sequence is unchanged.

The five specifically selected rows changed from Foreign/Opaque in R297 to Transparent/Structured in R327: instantiated `Iterator::try_fold` functions 36 and 38, `ControlFlow::branch` 37, `ControlFlow::from_output` 39, and `ControlFlow::from_residual` 40. Functions 36 and 38 keep one unknown region binder apiece but have no free type parameters or explicit trait clauses in the concrete instantiated rows. Their newly visible bodies call opaque slice-iterator `next` (10) and opaque `FnMut::call_mut` (47), as well as the newly structured ControlFlow methods. The report and companion JSON record decoded signatures, body ASTs, call arguments, relevant ADT references, and the remaining reachable opaque leaves and their region/constraint counts.

The generic source declaration was R294 Fun58, with a region binder, five generic types and four trait clauses plus one associated-type constraint. R322 records the associated source bounds and exact `iterator.rs` span. The concrete R327 body emission does not remove these source-level constraints.

R303's earlier translation error on R297 was `Unexpected erased region`. R330 later attempted R327 with the pinned R312 Aeneas binary and stopped earlier at `Nested-loop returns require exactly one Option language item` on the try_fold span, in `PrePasses.ml:969`. R331 inventories the exact prepass source and the three Option-instantiated type declarations found in R327. No route or proof claim is proposed by either audit.

The five status changes above are matched by exact selected function identity and signatures. LLBC `def_id` values are table-local positions and may shift across extraction variants; an earlier numeric-ID-only status pairing was removed. For example, Fun47 denotes the `Iterator::any` closure drop glue in R297 but the `FnMut::call_mut` implementation in R327. Do not interpret equal numeric IDs as equal functions. The call-edge inventory identifies `FnMut::call_mut` as an opaque dependency of the newly structured try_fold body.

R330 is the current attempted translation failure: `Nested-loop returns require exactly one Option language item` at `iterator.rs:2486:4–2490:35` (`PrePasses.ml:969`). R303's erased-region error on R297 is historical and not the current first failure.
