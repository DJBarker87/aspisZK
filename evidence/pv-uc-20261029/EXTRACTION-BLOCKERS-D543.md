# D543 checked extraction blockers

The 1,000-pair native differential passes. The full-entry Lean gate remains open. No production Rust, generated semantic body, extractor, library object or comparator was changed in this continuation.

## Emitted decoder shift does not type-check

`lean75000` compiles verbatim `PVUCDecoder.Types`. `lean75001` rejects verbatim `PVUCDecoder.Funs` at line 80:

```text
The argument 32#i32 has type IScalar IScalarTy.I32
but is expected to have type U32
in the application U64.wrapping_shl i5 32#i32
```

This is the emitted `wallet.long` operation for the final Rust decoder's `<<32`. The accepted ae1-2 translator produced this body; all 5,673 h4 external objects were verified before compilation. It is an elaboration failure, not an environment refusal, timeout or memory kill. The failed source hash is retained and guarded against unchanged resubmission. No replacement literal, shadowing function or alternate library was installed. Consequently the prepared emitted/native executable decoder comparison is **not run**, and no new D188 fidelity credit follows from these compiles. The existing N75140 native instruction-trace check retains its original limited scope.

## Full-entry external carriers and operations remain unbound

`lean75002` stops at the absent `PVUCEntry.TypesExternal.olean`. This is the explicit missing faithful-model dependency, classified as pre-elaboration environment failure. The 25 type and 119 operation declarations remain only in their original generated **uninstalled axiom templates** (`external-boundaries.json`). No full-entry Types/Funs object or standard-axioms result exists. Compiling the decoder's type file does not satisfy this gate.

## An external formatter alone cannot repair erased arguments

Final source `wallet.rs:42` opens `format!("/proc/self/fd/{fd}")` after the public `fd > 2` guard. Emitted full-entry `Funs.lean:1827`–1839 calls builtin `core.fmt.rt.Argument.new_display` and `core.fmt.Arguments.new` before the opaque `alloc.fmt.format`. The authoritative formatting profile maps both argument carriers to Unit and discards their operands. Observable JSON printing at lines 3886–3892 reaches the same erasure mechanism.

`lean75003` compiles `PV_UC_FormattingObstruction.fdArguments_equal` and `no_faithful_fd_formatter`. These show that the emitted argument construction is identical for any two values, and no pure external formatter receiving only those arguments can return both distinct required FD paths. Printed axioms are exactly `propext`, `Classical.choice`, `Quot.sound`; the final raw-walk audit is separate. These are diagnostic negative results about the existing model, **not credited formatter source laws or privacy-premise removals**. No rejecting-writer instance or unreachability assumption is invented.

N75147 validates the exact reached Rust formatting expression under optimized Rust 1.94.1: input 3 gives `/proc/self/fd/3`, input 4 gives `/proc/self/fd/4`. It is finite expression validation, not whole-function equivalence, FD custody validation or a D525 wire-format mismatch. N75146 had stopped before compilation because the own diagnostic wrapper omitted rustc's PATH; N75147 records the corrected absolute tool path and reuses the exact retained partial directory. Both receipts remain.

The no-go result rules out filling just `alloc.fmt.format` with a faithful definition under this erased interface. `(fmt-1)` still requires faithful writer/error-state semantics on observable formatting, or approved source removal. Neither the standard-axioms diagnostic nor native output equality discharges native I/O, JSON, hashing, prover, observer or whole-client side-channel associations.

The next formal deliverable is a source-faithful resolution of the shift/library typing mismatch and the formatting information loss, followed by faithful external bindings and a new full-entry compile. Any client/source or artifact change must reassess the covered frozen native gates. Existing native successes are not replayed unchanged, and no T field or endpoint hypothesis is added to bypass these gaps.
