# Projected wrapper order and conditional source composition

The callback cut copies the pinned candidate evaluator callback and proves it equals the already checked Closure2 callback. The wrapper cut factors only the low-weight prelude; it preserves the actual order: low reads/folds, leading packed call, full packed call, internal call, prepared-weight map, prepared-block construction, output callback. Its equality theorem assumes no successful source calls, so it preserves Result failure/divergence order.

The success adapter derives low-weight reads, multiplier preparation and the final output-array call using existing proofs. It remains conditional on the actual success and canonicality of all three supplied branch results. These are explicit remaining premises, not a whole-evaluator or end-to-end soundness claim. The subsequent work derives the internal branch from its already proved actual caller and derives the two packed branches from their pending actual callers.

There are four standard-only axiom reports over the three newly checked modules. Exact source, compiler, direct import hashes, source revision, commands, exit, wall time, peak RSS, process swap and object hashes are in the receipts. All accepted jobs used the serial focused Mac lane and zero process swap. No runtime-source or SBF/deployed-artifact changes are made.

The copied source bodies retain candidate Funs pin f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c (callback lines1055–1085, wrapper lines2691–2733). This is explicitly a source-cut proof: no checked whole candidate Funs object or theorem equating its declaration to this helper namespace is claimed. That source correspondence and the end-to-end 100-bit security/privacy proof remain open.
