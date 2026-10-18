# Adaptive factorization failure and sequential fresh sampling

Six checked modules connect the executable factorization program to a global probability bound. They are part of the efficient-extractor construction, not a completed spend-security theorem.

## Closed statements

`CompPolySplitStateClosure` proves that actual returned child factors stay monic, split and separable. Any such input with degree greater than one has two distinct actual roots, so the existing per-node retry theorem applies throughout recursion without an extra root-existence premise.

`CompPolyFactorMeanTools` reuses the existing independent-answer Program/eval/bind semantics, FS scalar mean linearity, and GenericNoHitFS2 monotonicity. Its lightweight outcome adapters reuse the constant/congruence proof shapes from R572SequentialWordMass without pulling in unrelated rejection-sampler modules. `CompPolyFactorTwoChildBound` isolates the child-abort union calculation.

`CompPolyFactorAbortBound.independent_factor_abort_le` proves the entire adaptive factorization program aborts with probability at most `(degree(f)-1) * 2^-t` in the existing fresh independent-answer interpreter. Later input factors may depend on earlier probe results. It includes every retry/child abort and proves fuel sufficiency when `degree(f) < fuel`. There is no work/grinding credit and no assumed global density bound: each node uses the already checked actual retry bound plus preserved algebraic state. The proof distributes the degree budget between the actual two child factors.

`SequentialFreshProgram` is executable: it follows the same adaptive continuations while replacing heap query addresses with a strictly increasing tape cursor. It proves actual `FreshFrom` for every table whose future is empty, and then applies the existing first-read interpreter law. Its outcome law is exactly that of the independent-answer interpreter.

`CompPolySequentialAbortBound` composes the two results. For its sequential fresh root-finder program, monic positive-degree input and q=card K in odd characteristic imply abort probability at most `(degree(p)-1) * 2^-t`, including the normalized root-factor projection. The fresh sampler here is the formal lazy sampler of independent uniform field-tape blocks, not the deployed Rust hash sampler.

## Remaining obligations

Follow-on packet [sequential-root-sampler-contract-20261019](../sequential-root-sampler-contract-20261019/README.md) closes successful-output correctness and the actual query-trace/cursor bound for this same sequential program, and proves its exact finite uniform field-tape law. The concrete random-bit-to-field sampler and total arithmetic/bit costs remain open. No production randomness implementation is equated here.

The Option RR traversal, actual WideExact GRS conversions, normalized vector children, filtering/message inversion, joint-list/caller count and whole-extractor operation/bit costs still need composition. The earlier numeric 395,412,192-site/149-trial/2^-120 statement remains conditional until those caller counts and all other failure terms are proved. Full source/sampler/terminal soundness and privacy coupling remain open.

## Evidence and proof-shape repair

Every accepted receipt records exact target/source revision, source/object/direct-import hashes, command, exit status, wall time, process RSS, process swaps and standard-only axiom reports. Native pinned Lean4.32 and existing caches were reused under -M2048 and a 4GiB aggregate local Lean RSS watchdog. Process swaps were zero; pre-existing host swap was not zero and is recorded separately. No full regression was repeated.

The initial monolithic probability proof hit 200,000 heartbeats at a nested child inequality. Isolating that calculation exposed an addition-lemma orientation issue and a generated-matcher elaboration mismatch. The accepted child lemma uses direct interpreter monotonicity, followed by the factored main theorem; the main proof passed in 2.53s without increasing its heartbeat or memory limit. The failed source/log/receipt and diagnostic attempts are preserved under history. No theorem with sorryAx is accepted.
