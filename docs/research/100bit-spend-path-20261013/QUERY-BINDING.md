# Concrete query and residual binding

2026-10-13. The query part now has checked algebra and independent-answer
probability theorems. This is not the complete R1 source, semantic, shared-oracle
Fiat–Shamir, or zero-knowledge theorem.

`MatchingSupport` defines the exact set of original log-18 positions where
both fold equations hold. Under `ConcreteBinding`'s existing four bad-set
exclusions, nonzero gamma, and accepted pairing equations, 9558 matching
positions imply a candidate in the literal joint list with all six functional
claims. Consequently, false claims imply that this fixed set has at most
9557 positions. The final message and both committed words are fixed in this
statement; the set is independent of the later query and rho challenges.

`ResidualBatch` forms the 22-coefficient polynomial whose coefficients are the
second-fold discrepancies at the queried parents. A nonzero polynomial has
degree at most 21 and at most 21 roots in the embedded subfield. Its zero
polynomial case is handled explicitly and means every residual is zero.

`NaturalEmbedding` proves compatibility of the natural line basis with any
field embedding. Compatibility with the M31 algebra map follows from uniqueness
of the prime-field homomorphism, without an extra compatibility premise.
`QueryAccumulator` proves the four closed forms of the explicit recurrence:
query index, rho power, 64 accumulated subfield weights, and accumulated
wide-field right-hand side. `QueryResidualBridge` composes those identities
with the actual stored log-16 encoder. Acceptance of the recurrence's final
dot-product equation, and the per-query first-fold checks, puts every query in
the matching set outside the 21-element rho exception.

This closes an algebraic interface: the weights may live in the subfield while
the final message, folded values, and residual polynomial live in the wide
field. These are canonical field elements in Lean. The result does not by
itself prove parsing, checkpoint restoration, or Rust arithmetic correspondence.

## Probability scope

`BoundedQueries.no_claims_bounded_q22` applies the existing stopped sampler
law directly to the concrete matching set. Under its formal independent-answer
semantics, the probability mass of successfully returning 22 queries all in
that set is at most

    choose(9557, 22) / choose(262144, 22).

Sampling exhaustion contributes zero. No success-conditioned distribution or
assumption that all scans succeed is used. The legacy factor `1 + delta0` is
not necessary for this exact query law; it remains a conservative envelope in
the arithmetic ledger.

`RhoSamplerBound` applies the existing modulo-fiber counting theorem to the
actual residual set. For a specified rank encoding from B equally likely
inputs to an n-element field, the bad-event mass is at most

    21 * (floor(B/n) + 1) / B.

The input and output rank encodings are explicit equivalences. For B=2^256
and n=P^4, Lean also checks that this is below 2^-119. The ledger gives the
more precise approximately 119.608-bit value. `RhoAcceptance` proves the
accepted-event implication: if even one fixed query misses the matching set,
the field-level query checks can pass only on this counted rho exception.
Thus the density theorem bounds acceptance in that case, not merely an
unrelated polynomial-root event.

Connecting these fresh-answer laws to the concrete shared transcript is still
required. In particular, R1 eagerly reads eight squeeze/advance pairs but
retains the stopped scan state. Existing first-read/spawn machinery is relevant;
a generic independent-draw claim cannot substitute for that connection.
Merkle extraction/binding must also justify using fixed words when the proof's
openings arrive after rho. `QUERY-FS-INVENTORY.md` records those interfaces.

## Supporting coefficient identities

`RawFunctionalWeights` constructs all seven functionals from explicit subfield
row vectors and proves the materialized kappa-weighted coefficient formula.
`RawPairing` transports this sum through both dual folds and the final dot
product. These results connect two mathematical descriptions of the pairing;
they do not yet identify the optimized Rust constructors with the seven vectors.
`RawOpening` and the root-checked `RawQueryBound` instantiate the deterministic
claims, accepted pairing and bounded-query consequence with those explicit rows.

`D18Transport` proves the five-digit permutation tau=[3,4,2,0,1] is an involution
using symbolic radix-four arithmetic. It supplies a self-inverse `Fin 1024`
equivalence. Rust's bit shifts/OR and the three semantic point weight vectors
still need explicit correspondence; this arithmetic equivalence alone is not
that proof. `FUNCTIONAL-INVENTORY.md` identifies the existing semantic APIs.

## Focused verification

All selected new targets have successful NUC checks under MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0. Exact source hashes, attempts, times, peak RSS,
zero-swap records and printed axioms are validated by
`evidence/lean-query-chain-20261013/validate_manifest.py`.
The final root checks for `QueryResidualBridge`, `BoundedQueries`, and
`RhoSamplerBound` used at most 3,157,812 KiB peak RSS
(about 3.02 GiB), and took 1.28–1.73 seconds each. The axioms are
`[propext, Classical.choice, Quot.sound]`; D18 arithmetic uses only
`[propext, Quot.sound]`. No successful selected target uses `sorryAx`.

The query-law dependency replay rebuilt 32 affected modules and reused four
pinned leaves. Seven existing files received narrow explicit imports, with
non-import bodies byte-identical. `ModuloCounting` separately received two
explicit tactic imports and a focused check. This avoids loading all of
Mathlib's tactics. The source and cache receipts are retained, including failed
attempts. This was a focused dependency replay, not a full release replay or
complete historical object-provenance audit.
