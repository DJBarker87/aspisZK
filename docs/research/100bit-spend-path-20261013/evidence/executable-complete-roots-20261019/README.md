# Executable recursive factorization and complete root lists

This packet turns the preceding executable split/retry primitive into a bounded recursive root finder. It closes success correctness; it does not yet prove its global abort probability or a complete polynomial runtime bound.

## Checked statements

- `CompPolySplitFactorQuality`: any returned trial/retry factor is a monic proper divisor. Executable monic division produces a monic complementary factor; both children have positive degree strictly smaller than the parent and their product is exactly the parent.
- `CompPolyFactorRecursion`: the executable fuel-bounded binary factorizer returns `none` on exhausted fuel or any retry/child failure. Every successful run returns a complete product of linear factors for the exact input. Child retry tapes use distinct intended binary-heap addresses; fresh independent sampling and the formal no-reuse/randomness argument remain open.
- `CompPolyFactorCertificate`: successful factorization returns exactly all actual roots, and its output length equals input degree, counting multiplicities.
- `CompPolyCompleteRoots`: executable modular power and normalized gcd compute the previously proved squarefree split root factor. For monic positive-degree input and q=card K, a successful root-finder run returns exactly every actual root, with no duplicate and output length at most input degree. The implementation neither enumerates the field nor constructs a dense X^q. The success theorem is conditional on an actual `some roots` result; it is not a probability-of-success theorem.
- `CompPolyFactorSplitCount`: the conservative full child-tree split count is at most input degree minus one, independently of tape values, under input monicity.
- `CompPolyFactorCounted`: an instrumented execution produces exactly the same Option result as the real factorizer. Its retry-call counter follows actual early-abort behavior and is bounded by the conservative tree count, hence by input degree minus one. The ghost counter is explicitly connected to executed control flow, not simply assigned a desired budget.

## Remaining extraction obligations

The existing per-node retry bound 2^-t must be combined across adaptively selected factors using fresh independent tapes, with a proof that the actual random sampler supplies that law and does not reuse node tapes. Fuel sufficiency, aggregate gcd/modular-power/field/bit operation costs, and the Option-returning RR traversal must be connected to this backend. The library's total FieldRootContext cannot directly accept a possibly aborting backend; substituting an empty list on failure would be unsound for completeness. No deterministic field-enumeration fallback is used or proposed here.

The full protocol source/sampler/terminal premises and privacy coupling remain separate open obligations. No production source, deployed artifact or security parameter changes in this packet. No end-to-end 100-bit proof is claimed.

## Evidence

All six accepted focused checks exited zero using pinned Lean 4.32 and existing compiled caches. Receipts record exact source revision, source/object and direct-import hashes, command, wall time, RSS, process swaps and standard-only axiom reports. Process swaps were zero; pre-existing host swap is recorded separately and was not zero. Local checks use -M2048 and a 4 GiB aggregate Lean RSS watchdog. CompPoly and mathlib pins are the same as the preceding executable-cz-backend packet. Original receipts are preserved: a missing custom-import source field is resolved through the corresponding producer object hash in the two accepted manifests. No unchanged full regression was rerun.
