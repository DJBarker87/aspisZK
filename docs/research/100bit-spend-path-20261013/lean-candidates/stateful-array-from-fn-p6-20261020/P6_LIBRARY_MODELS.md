# P6 library model: `core::array::from_fn`

This is a harness-only model. It does not alter generated output or production Rust.

`AspisR1FromFnP6.statefulFromFnRun` models one callback step as
`step state index : Result (value × nextState)`, then recurses at the next
ascending index. A successful execution is equivalent to
`StatefulFromFnTrace`: exactly one successful callback transition at every
index in order, the output list in that same order, and the final closure
state after the last call. `statefulFromFnTrace_preserves` lifts any checked
per-step state/value invariant across that trace. `Result` failures and
divergence propagate through the model; the successful trace theorem does not
assume callback totality.

This operational model matches the Rust library's documented ascending
callback order and stateful closure use. The retained Rust source pin is
`docs/research/v8-full-view-zk-20260912/evidence/r67-circle-source/stdlib-source/array/mod.rs`
(SHA-256 `fa149bb7f1e856350ccbf94cd402f368ec7f613b8a1d1eeeafffe85b5e75277f`),
which shows `from_fn` wrapping the closure and calling `try_from_fn`; the
latter delegates array initialization to `try_from_fn_erased`.

The differential test in `sources/from_fn_differential.rs` compares actual
`std::array::from_fn` with the explicit ascending-loop model. It checks output
values, each observed index, and final captured state for lengths 0, 1, 4, 8,
16, and 29, with four state seeds/multipliers. Length 29 is the current powers
call-site length. It passed on the host's pinned Rust 1.93.0 compiler
(commit `254b59607d4417e9dffbc307138ae5c86280fe4c`, rustc binary SHA-256
`87b02c67012c28083fe485a50b10470a662c828c6e2cd0caf4775e00986cdfc8`).
The Rust source archive is historical; the differential test exercises the
installed 1.93.0 standard library directly.

The Lean model target was compiled with Lean 4.32 in a fresh NUC scope
(MemoryHigh 1 GiB, MemoryMax 2 GiB, MemorySwapMax 0). Its theorem axioms are
standard only: `[propext]`, `[propext, Quot.sound]`, and `[propext]` for the
success/trace equivalence, invariant preservation, and trace length results.

P6 remains a reviewed library-model boundary, not a proof of the compiler's
Rust standard-library implementation for every possible callback. A concrete
callback adapter must still show how its Aeneas `FnMut` result/back values
instantiate `step`; the current powers-specific consumer is being handled
separately. No general claim about all `from_fn` users is made.
