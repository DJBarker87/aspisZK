# Recovery is fixed before the three commitment reads

The canonical finite-query model now proves that later oracle queries cannot
change the entire recovered leaf function for C1, C2, or the folded root,
outside one explicitly bounded family of hash events. The function includes
missing entries: an entry unavailable before the commitment cannot become
available later outside those events. This closes a model-level causal
availability obligation. It does not yet establish an efficient witness
extractor, the complete Fiat–Shamir theorem, privacy, or Rust correspondence.

## What is fixed, and when

`CanonicalRecoveryStability.recoverAt` parses the canonical records in a
query trace, follows the selected eight-way Merkle path by finite lookup,
and returns either the exact `(packed bytes, salt)` or `none`.
`recover_stable` equates this function on a prefix and on its full extension
when the prefix already contains a hash input naming the root. Its premises
are full-trace consistency, the distinct-read bound, input length bounds,
and absence of the three specified collision/target events.

The proof is bidirectional. A successful first-match lookup persists under
appending records. In the other direction, a successful later lookup yields
an actual recorded leaf and path. Their literal hash inputs are already in
the full canonical log, so the previous recovery theorem applies without
an extra assumption that a separately supplied opening trace was executed.
This also proves that an earlier `none` remains `none`.

The specialized word theorems move the equality to **before** the commitment
frame's oracle read. Adding that single record cannot alter either Merkle
lookup table:

| Commitment | Reason its frame is not a Merkle record | Checked function equality |
|---|---|---|
| C1 | Initial byte 85 differs from node byte 24 and leaf byte 16 | `C1BeforeFrameStability.c1_word_stable` |
| C2 | Frame length 71 differs from node length 257 and salted leaf length 162 | `LaterCommitmentStability.c2_word_stable` |
| Folded root | Frame length 294 differs from those same node/leaf lengths | `LaterCommitmentStability.folded_word_stable` |

These are equalities for every slot path simultaneously, not a union bound
over opened leaves. Applying a fixed default to missing entries therefore
also produces the same completed word. Selecting the correct first-read
cut in the actual verifier execution remains part of protocol composition.

## One common trace and one hash-event budget

`CanonicalFullTraceRecovery` and `ThreeCommitmentFullTrace` allow arbitrary
intervening queries and other openings. Their events and read bound refer
to the same complete trace. Consistency follows from the oracle evaluator
when that trace is instantiated by an execution.

`CombinedMerkleTargets` combines eight child readers and two root readers.
`CombinedMerkleCollision.mass` joins these with the existing duplex event:

```
Pr[combined hash event] <= 12 * Qtot^2 / 2^256.
```

This theorem quantifies over the same arbitrary prover and verifier oracle
programs and assumes their complete experiment has at most `Qtot` distinct
first reads for every oracle. The existing trailing-state event is already
one of the two root readers. `old_included` checks this inclusion; adding
the old three-term budget separately would count that reader twice.
`outside` provides exactly the three event exclusions used by recovery.

The inequality is a hash-event result, not a full soundness or knowledge
bound. No final security ledger is replaced by it. The round-error term,
query factor, and accepted-proof/extraction containment still need their
joint instantiation. Honest-run query counts are not adversarial bounds.

## Geometry and finite enumeration

`MerkleIndexGeometry` proves the base-eight slot encoding has the stated
depth and inverts back to the original in-range index. At depth six it is
injective on the 262,144 fibres. It also proves
`u = 4 * (u / 4) + u % 4` with the folded index bounded by 65,536.
The [source map](MERKLE-GEOMETRY-SOURCE-MAP.md) records the matching Rust
formulas, including the folded tree's zero-payload padding and private salts.
This is not a formal refinement of the Rust implementation.

`RecoveredRootRecorded.canonical_root_read` proves that successful recovery
along a nonempty path uses a root that appears as an earlier recorded oracle
output. This permits finite enumeration of candidate roots from the table;
it does not establish the complexity or correctness of a complete spend
witness extractor. In particular, the existing `Classical.choose` existence
extractors and finite-filter GS decoder specifications do not provide that
algorithm by themselves.

## Reuse and remaining composition

The proof reuses the repository's finite Merkle lookup and parser soundness,
literal path evaluator, canonical-log consistency, parsed first-hit target
bounds, and `FS2.Duplex.noColl_injective` / `coll_mass`. New append and
recorded-path lemmas supply the deterministic links between those results.

The old `FS2.D2` still quantifies over arbitrary pairs of tables. These new
theorems concern causally related prefixes of one actual execution; they
do not discharge that arbitrary-table premise. The next security argument
must define a concrete causal first-hit classifier and prove its local
density and accepted-proof containment, or justify another valid knowledge
reduction. No classifier or theorem premise has been silently weakened.

The [terminal-oracle transport](TERMINAL-ORACLE-TRANSPORT.md) is a separate
checked checkpoint. It reuses the completed 33-row decoder proof when
a terminal oracle-reading decision is included. The actual terminal decision,
field canonicality, checkpoint lifecycle, efficient extraction, and privacy
simulation remain obligations.

## Focused evidence

Base revision: `b0285d5afb56f158014470de4a87730547ab5738`. Each changed
component was checked individually in the pinned NUC workspace. The final
`R1CausalCommitmentCheckpoint` ran once after those checks: exit 0,
0.72 seconds, peak RSS 1,801,596 KiB, zero swap, limits 4G/6G/zero-swap.
Its source SHA-256 is
`f86993d5f3088fdbd4a5e67f9e37dbc67b8bb09c9b8a53e36f2fffd591e86c5e`.
All fourteen checkpoint axiom reports use only `propext`, `Classical.choice`,
and `Quot.sound`. Exact sources, failed attempts, receipts, resource logs,
object hashes and the root audit are retained in
`evidence/lean-causal-commitment-20261014/`.
