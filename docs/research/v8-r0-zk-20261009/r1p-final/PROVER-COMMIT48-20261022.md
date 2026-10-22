# Part 48: shipped simulator binding and payload image

**Target not yet established.** Work in progress on
`codex/cx-prover-commit48-20261022`, based on `26b922be6`.

D164 scope: shipped per-iteration Kani bindings, Lean induction over the owned
loops, then the complete native simulator payload byte image. No Aeneas on
shipped code. No FSExperiments conversion, joins or endpoint changes.

## Stage 1: native evaluator iteration binding

The per-call abstraction records operation tags and every operand, and feeds
arbitrary symbolic results back to both sides at corresponding calls. Equality
of the complete call trace and result establishes a parametric control-flow
binding; it does not prove an arithmetic callee contract. Part 47's separately
checked release arithmetic is reused only at its exact pinned source bodies.
The harness must cover the full 1024/512 array shapes and arbitrary legal
iteration indices; short whole-loop fixtures do not replace this obligation.

## Endpoint before/after

`../../100bit-spend-path-20261013/evidence/prover-commit48-20261022/endpoint/`
contains verbatim complete before/after snapshots, copied from part 47.
They are unchanged. The deployed theorem still requires
`RustProverRefinement`; the D159 L1 obligations remain open.

## Validation and trust

Only attempts J9900–J9999 are allocated to this job. Host compile receipts
will record target, source SHA, dependency fingerprint, exit, wall, peak RSS,
swap, source revision and every printed axiom. Host jobs use MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and the requested linker flags.
No shipped source has changed. The current S4 ELF pins apply to any later
shipped change. No wallet keys, funds, push or merge are involved.
