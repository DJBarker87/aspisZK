# Semantic prefix to R1 extraction

This checkpoint connects the first 25 masked semantic rounds to the R1
opening candidate. It is a checked field-model implication. It does not
instantiate Rust, Merkle authentication, a shared random oracle, or privacy.

`SemanticCandidateList.candidate_mem_iff_old_Lambda` proves that the literal
R1 and R0 candidate predicates have the same 38,230-position joint-agreement
filter. `rowsOf_candidate_mem_LambdaRows` transports an R1 coefficient tuple
to the old row-space list. No candidate uniqueness or new list-size premise
is introduced.

`SemanticHit.no_hitFrom_iff_all_semanticBadZ_excluded` proves, for a parsed
prefix of at most 25 semantic rows, that the old recursive hit predicate is
equivalent to a hit in the semantic classifier at one of those rows. The
proof is a list induction. Nonsemantic tags cannot occur in a parsed
semantic slot. This equivalence prevents the new bridge from implicitly
assuming the old circle or five-row opening protocol.

`SemanticPrefix.outsideBad_of_prefix` derives all six fields of
`MaskedSemantic.OutsideBad` for every R1 candidate from the parsed 25-row
prefix and absence of a semantic hit. It applies the unchanged
`no_hit_early`, `earlyRounds_cover`, `no_hit_eta`, and `no_hit_alpha` results.
The final `large_matching_extracts_of_prefix` takes the explicit per-row
semantic exclusions and composes them with the current two-fold opening.
Its conclusion retains literal R1 list membership, production constraints,
copy-link balance, and the existing `InputNoteExtracted` relation.

## Why the early challenges remain causal

The final H1/G words are chosen after lambda and chi. Unioning over their
final candidate list as though it were fixed before lambda would be wrong.
The reused proof instead maps each final candidate to a trace with lanes 26
and 27 set to zero. This padded trace belongs to a list fixed by C1 alone,
and has the same lambda/chi bad events. That list still has at most 100
members. From theta onward, the actual H1/G words are fixed and the original
candidate belongs to the prefix's list. This is the existing proved padding
argument, now connected to the literal R1 candidate through list equality.

Eta follows the mask-sum claim at row 14. Its event covers every candidate's
own mask sum and original sum. Alpha rows 15–24 each use the polynomial
already sent at that row and the earlier alpha challenges. The degree bound
comes from the accepted semantic checks, not from a new assumption that the
prover supplied honest polynomials.

## Semantic row accounting

The unchanged `semantic_round_densityZ` bounds each classifier at a fixed
pre-challenge prefix under the independent-answer `semChal` law. With
`P = 2^31-1`, `deltaQ = P^4/2^256`, and
`atom = (1+deltaQ)/P^4`, `SemanticBudget.budget_eq` identifies its 25 bounds
with the following candidate-unioned root counts times `atom`:

| Rows | Challenge | Count per row | Number of rows |
|---|---|---:|---:|
| 0 | lambda | 217,600 | 1 |
| 1 | chi | 54,400 | 1 |
| 2 | theta | 2,800 | 1 |
| 3–12 | zerocheck coordinates | 100 | 10 |
| 13 | mu | 200 | 1 |
| 14 | eta | 100 | 1 |
| 15–24 | alpha | 2,700 | 10 |

`SemanticBudget.budget_sum` proves that their sum is exactly
`303100 * atom`, approximately `2^-105.7906`. This is arithmetic over the
prefix-conditional bounds. It is not a new end-to-end soundness probability
or a replacement for the shared-oracle reduction. In particular, a
per-oracle-query coefficient and an adversary's total success probability
must remain distinct; no work or grinding credit is used here.

## Explicit remaining interfaces

The bridge takes the parsed challenges, mask claim, ten polynomials, and C2
words, together with equalities identifying the R1 words with those C2 words
and the transport with D18 `rowEquiv`. It also needs public/word typing,
the accepted semantic equations, and the opening's existing matching,
pairing, and bad-set-exclusion premises. These are model inputs; the theorem
does not derive them from authenticated Rust proof bytes.

The source inventory in `TRANSCRIPT-R1-INVENTORY.md` confirms the intended
ordering of C1, lambda/chi, C2, theta/zc/mu, eta, and alpha in the P3 cost
probe. That inspection is not formal source correspondence. The new opening
adds its own fold/query/rho schedule. The old 32-round D3 or Fiat–Shamir
theorem is not applied to that schedule. Full settlement/output-value
extraction and zero knowledge remain separate obligations.

The subsequent [`SPEND-NOTE-BRIDGE.md`](SPEND-NOTE-BRIDGE.md) checkpoint
discharges the bounded-value and output-note extension. Its
`strengthen_candidate_result` accepts this prefix theorem's conclusion
without additional semantic premises. Append/settlement correctness,
source correspondence, shared-oracle accounting, and privacy remain open.

## Verification

The final `R1SemanticPrefixCheckpoint` passed on the NUC in 1.38 s with
3,566,892 KiB peak RSS and zero swap. Its seven axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Every job used the pinned
runner with `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`.

Nine unchanged historical dependency modules were refreshed after stale
namespace references were identified. A local recursion-depth failure in
the list transport was fixed by keeping the large list definitions opaque
and applying the symbolic membership lemma; limits were not raised. The
focused sources, intermediate failures, receipts, and produced objects are
retained in `evidence/lean-semantic-prefix-20261013/`. This is a focused
checkpoint, not a fresh replay of the historical release manifest.
