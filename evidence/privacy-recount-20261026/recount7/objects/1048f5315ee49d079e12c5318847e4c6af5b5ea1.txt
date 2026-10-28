# Unaccepted continuation drafts — NO proof credit

The four .lean.draft.txt files are archived drafts, not importable proof modules.
Every final imported PV_L2C module must have an accepted matching-source receipt.

OwnedBalance: attempt 42696 failed at the rewritten mutation continuation,
where the simplifier's instances transparency cannot identify the Slice and
Vec aliases. The generic VecShape length and read lemmas pass at 42695; the
selected-row traversal and vector-write projection pass at 42674/42673.
Next proposed fix: name the backward function with an explicit
QM31 → alloc.vec.Vec QM31 type, prove its mutation equation before rewriting,
and then compose binds. This has not been compiled and carries no credit.

RowEnumeration, SelectedDense and ExtractedGuard have not been compiled. They
would transport the symbolic ascending row traversal into the excluded finite
sum and compose the complete owned result with the two padding predicates.
They are not included in the final audit or replay.

The separately executed native differential passed 128 same-input scalar/Q
cases, including changed dependent writes in all 128. This is finite validation,
not a complete Result law or a universal honest-family/native guard theorem.
Consequently a structural (K-1 substitute) whole native link is not credited.

Next sampler target: AspisR1ProverStep8.Funs contains the actual extracted
prover_commit_reference.limb_caller_loop.body / limb_caller_loop / limb_caller
and qm31_caller. A success-range invariant at the <P return branch, followed
through the library loop, is pointwise in the hash callback and does not need
an IID-word law. Native constructor/cursor safety and producer/table/caller
association still need proof; E1/E2 remain needed for the full stream coupling.
