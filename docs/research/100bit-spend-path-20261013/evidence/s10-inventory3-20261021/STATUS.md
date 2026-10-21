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

## Stage 2: frontier and order evidence

All 40 affected generic declarations now have a unique body in the **frozen
SBF compiler's MIR**, in both verifier builds. Pool contains 29 of those generic
bodies; absence of a verifier-only crate from the Pool build is not called a
missing Pool body. Thirty-six declarations have no type or const parameters;
regions and safety obligations are not thereby discharged. The four generic
helpers are powers (observed N=4/7/29), heap::filled (observed T=QM31/WideExact/
[u64;4]/u8), private_leaf_hash_with_digest (H), and parent_with_digest (H).
`generic-instantiation-review.json` records the observations and their limits.

Eight frontier records have exact raw-symbol matches in frozen compiler LLVM
output and the original linked ELF table. LLVM local mangled names can recur
in different codegen units: **all candidate definitions are retained**, rather
than overwriting one definition with another. This is partial codegen/source
provenance, not eight complete semantic refinements or a final inline map.
The eight-way parent helper has only a LegacyHashFn inline observation in a
source wrapper; no deployed instance witness was established. The job's forty
records cannot all be presumed to be already demonstrated deployed instances.

All 18 originally open entries have explicit specifications and disposition
categories in `open-frontier-specifications.json`. Owned source refinement,
owner acceptance and coherent import/replay obligations are not silently added
to library trust. Proposed boundary specifications are requirements, not new
axioms or evidence of their own truth.

Frozen MIR supplies 25 selected function CFGs, 65 selected calls and 140 block
dominance facts. In each verifier build, TX1's batch-0 Merkle call dominates
geometry and query evaluation; TX2's resume precedes batch-1 Merkle, which
dominates geometry/query evaluation and finishing. Thus source arithmetic and
checkpoint work is interleaved between batches. Mapping that execution to the
model prefix and six short-circuited slots still needs semantic caller proofs;
listing functions in source order or ELF address order cannot supply them.
`ordering-facts.json` retains four independently checked non-textual order facts.

The completeness gate exits **2**, with the exact output and resources in
`reconcile-receipt.json`. It has not been weakened to make missing source joins
pass. No headline premise is removed. **Target not yet established.**
