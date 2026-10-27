# Decision: how to repair D188 after finding D188-P3 (lead, 2026-10-27)

**APPROVED by the owner 2026-10-27 ("i gpo with all your recommendations"): the recommended option is adopted and recorded in SECURITY-CONTRACT-20261021.md, 'Owner-approved amendment, 2026-10-27 (second)'.**

## What happened

The owner-approved trust item D188 says the pinned Charon/Aeneas translation
of the release source is the semantics of each translated shipped body.
Finding D188-P3 (D188-PROVENANCE-FINDING-20261027.md) shows this is false for
`sampler::low_base_p_digits`. The pinned emission drops the `*limb = quotient`
write the frozen Rust performs, so on the block P it returns quotient P where
the Rust returns 0. The lead has corrected the claim. D188 does not credit that
body, and credit for four further functions in the same mutable-iterator
family is suspended pending checks:
- multiproof::verify_in_place
- verifier::update_residue_row
- sampler::add_small_base_p
- BatchedWeights::finish

The adopted soundness theorems are not contradicted: they reason about the
cohort sampler, which matches the native Rust on the measured blocks. What is
missing is a proved link from that model to the shipped function.

## Options

1. Narrow D188 and bridge natively (recommended). Exclude from D188 every
   translated body whose emission is shown unfaithful, and treat it exactly as
   the existing twelve opaque leaves are treated: a native P6 bridge from the
   frozen Rust to the cohort model the proofs already use (owned reference,
   Kani, Lean model). For the sampler, Kani checks the division-result relation
   (q*P + r = dividend, r < P) per limb step, which is easy for SAT, instead of
   division equivalence, with the eight-step composition in Lean. The four
   suspended functions are checked first; each one that fails joins the leaf
   list. This adds no trust: the trust surface shrinks, and the proof
   obligations grow by one to five leaves. The target, metric, adversary,
   contract statement and implementation are unchanged.
2. Re-pin the translator (route A). Adopt a Charon/Aeneas version whose
   emission of mutable-iterator restoration is faithful, re-extract, and redo
   the D188 provenance work. Route A was not approved on 2026-10-27, and it
   would still need the same per-function fidelity checks, since translator
   fidelity is exactly what has now failed once.
3. Keep D188 as stated. Not acceptable: it is now known to be false for a
   shipped body.

## Recommendation

Option 1. It is the smallest change that keeps the release argument honest. It
reuses the P6 machinery and the ruling already in force for opaque leaves, and
it changes no target or implementation. Until the owner decides, the lead
proceeds only with work valid under every option: the per-function fidelity
check of the four suspended functions. No trust credit is taken for any of the
five functions.
