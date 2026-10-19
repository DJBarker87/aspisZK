The selected standard-library mutable-enumeration method now has a focused
source extraction and a checked comparison with the runtime used by the rho
finish proof. This is a component result. Composition through finish and the
actual verifier callers is still required.

Pinned source and extraction boundary
------------------------------------

The compiler is nightly-2026-06-01, rustc commit
14210df0e27ccd7d9e6a05b8085cbd438e4bbc65. The retained source files and
`iterator-host-pins.json` pin standard-library source, tools, reused full-MIR
sysroot and LLBC hashes. No tool binary or sysroot object is committed.

`extract-iterator.py --check` validates the original Enumerate struct and the
exact next body. Its specialization substitutes
`I := core::slice::IterMut<'a,T>` and
`<I as Iterator>::Item := &'a mut T`, expresses the return type as Self::Item,
and retains the method body byte-for-byte. The internal overflow attribute is
replaced by explicit release overflow checks in the extraction environment.
The proofs compare the checked operation, including its failure behavior.

`extract-borrow-option.py --check` validates the exact Option branch and
FromResidual bodies at the borrowed types used by this method. A local trait
and a free-function signature permit extraction without violating Rust's
orphan rules. Both bodies are unchanged. Structural type specialization and
the usual Rust/Charon/Aeneas frontend correctness remain the explicit trusted
source-extraction boundary; this work is not a proof of those compilers.

`emit-iterator.py --check` pins the three emitted function declarations.
It omits unused generic trait-instance objects, whose generic signatures do
not carry the concrete borrow handback. The selected emitted function bodies
are unchanged. The imported `SourceOption` name adapters use the emitted
borrowed branch directly. Its generic residual adapter is proved equal to the
actual emitted pair specialization by `residual_specialization`.

What Lean checks
----------------

`CuSavingsIteratorSource.source_none` and `.source_some` identify the complete
emitted next method with its two execution paths and actual handbacks.
`CuSavingsIteratorBridge.source_model_write_eq` compares that source with the
existing concrete runtime for every iterator state and replacement item. It
preserves the returned option/value, entire forward iterator/counter state,
checked-counter failure/divergence, and inner iterator after writing through
the returned mutable reference. No cursor/canonicality bound is assumed.
The done-path lemmas also identify the unchanged inner iterator on exhaustion.

Whole backward Enumerate states are deliberately not equated. The source
handback captures the input count; the existing runtime keeps the supplied
later count. The proof compares their inner iterators after the writes used
by finish. Finish returns a slice and discards this backward counter. A
consuming finish-context theorem must establish that projection before this
comparison can discharge the remaining source-binding obligation.

Successful focused targets: `borrow-option-types-a`,
`borrow-option-operations-a`, `iterator-types-a`, `iterator-source-option-a`,
`iterator-next-a`, `iterator-source-shape-e`, `iterator-source-bridge-a`.
Each receipt includes command, source revision/hash, feature settings, exit,
wall time, peak RSS, process/cgroup swap and #print axioms. All exit zero,
use only standard Lean axioms, take less than two seconds, peak below 2.8 GiB
RSS and use zero process/cgroup swap. The source receipt audit covers 31
focused components and explicitly leaves the full goal incomplete.

Why the extraction path changed
------------------------------

The initial distributed-sysroot extraction left Enumerate opaque; including
the type resolved that error. Its optimized MIR then exposed an uninitialized
Option<Infallible> residual, rejected by Aeneas. Making FromResidual opaque did
not affect the already-inlined code. The existing full-MIR sysroot resolved
this without rebuilding a sysroot or changing any tool.

The generic method was translated but mapped to Aeneas's built-in interface,
which does not expose the concrete returned borrow. Charon partial mutable
monomorphization first required explicit flags already implied by its preset,
then panicked on trait-item substitution. Full monomorphization translated but
hit Aeneas's unsupported specialized Option type analysis. Those failures and
the successful concrete source-specialization receipts remain archived. They
are not proof successes. No memory limit was raised, no failed memory job was
restarted, and no unchanged full regression was repeated.

Production Rust and the measured ELF are unchanged. The full equivalence,
soundness transfer and privacy transfer remain open.
