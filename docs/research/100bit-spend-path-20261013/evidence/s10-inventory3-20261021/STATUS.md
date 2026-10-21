# S10 pass 3

## Stage 1: frozen compiler evidence

The private diagnostic builds reproduce all three frozen deployed ELFs exactly.
The 488 frozen source files independently rehash without mismatch. The compiler
is platform-tools v1.52, Rust 1.89.0-dev / LLVM 20.1.7, not the nightly diagnostic
compiler used in pass 2. No shipped source changes. No keys are inspected or
removed. No push or merge.

Build receipts retain commands, caps, wall time, peak RSS, swaps and source
revision. `build-manifest.json` retains the compiler output SHA-256/size and
generator; MIR and LLVM outputs stay on the host. The monomorphization logs are
small text evidence and are retained here. Build default v1 failed because this
compiler accepts `print-mono-items=yes`, not the historical `lazy` spelling.
Default v3 fixes missing per-compiler-output snapshots in v2; it is a changed
capture pipeline, not an unchanged regression replay. Only default v3 is the
primary default diagnostic snapshot. Devnet entry output was snapshotted after
its successful build and before any subsequent verifier compilation.

Every build ran in its own scope with MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, after the populated-scope reservation check.
Successful builds take 25–27 seconds, peak below 700 MiB, zero swaps. Exact
values and exit codes, including the failed preflight, are in the receipts.
`#print axioms`: N/A for this stage (compiler evidence, no Lean theorem).

Instance/inline correspondence, pointer-flow, owner acceptance and concrete
source Calls tree/order are not yet established by this stage. The existing
source-completeness gate is not changed or relabeled.
