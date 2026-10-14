# Ordinary-prefix, q22 and following-round composition

The checked trace connection now combines the earlier ordinary records,
the selected q22 path, and its following challenge. It derives the earlier
records from the table before that following round and uses one shared list
of missing hash answers. It reuses the existing record-completion,
first-read-order, background-sampler and adaptive-chain results.

This is an abstract codec and trace theorem. It is not the complete R1
Fiat–Shamir instance, a Rust refinement, or a private-spend security theorem.

## Moving recovery to the later table

`TableBeforeOrder` proves that a known cell in the table before one address
remains the same cell before a later address. Consistency supplies its value;
first-read order supplies its presence. No new collision event is added.

`OpeningPrefixAnchor.walk_before_anchor` applies the existing initialized
semantic/opening walk at that later table. The earlier anchor address carries
the final ordinary state. The proof transfers the opening cells and derives
the semantic cells using the last semantic advance, the explicit reseed
edge, and the earlier anchor. `OpeningAnchorCells` exposes those same cells
for the pending-answer argument. Neither theorem assumes the table lookups
or successful walk that it concludes.

## One answer for each address

`JointPrefixAnswers.missing` is the deduplicated union of the ordinary
prefix's missing squeeze addresses and q22's missing selected-path squeezes.
Both completion functions use one `DQ.accFrom` lookup on this union. The
proof does not assume that the two components' address lists are disjoint.
If an address appears in both, it receives the same answer in both.

With a coherent table, filling that list with the actual oracle answers
gives the actual ordinary completed rounds and the existing query-recovery
result. `PrefixPendingFacts` derives absence, trace reads, and separation
from the following round's absorb/squeeze/advance addresses, given known
absorbed states. `PrefixRecordFacts` supplies the corresponding list facts
for the literal semantic/boundary/opening record construction.

## Following and sampling the combined component

`JointNextTrace.follows_after_prefix_query` reuses `QueryOwnFollow.follow`
on the shared missing list. It derives freshness in the suffix starting at
the following absorb and returns the actual completed ordinary prefix, q22
result, and next challenge. The q22 recovery uses only its selected advance
prefix in the earlier table. Its unused tail need not precede that absorb.
The existing whole-trace premises still require all eight query pairs to
be read; this matches the inventoried fixed eight-pair computation but is
not itself a source-execution proof.

`OpeningQueryTrace.recover_and_follow` derives the known-state premises of
that theorem from the recovered ordinary chains. In particular, selected
q22 recovery proves that the query absorb precedes the following absorb;
the earlier-anchor results then recover all ordinary records at that later
table. Abstract indexed payload decoding gives the literal typed list.
For 27 semantic and four ordinary opening rows, the next challenge index is
32, as required for rho. The theorem proves both typed ordinary recovery
and the combined trace-following conclusion.

`JointNextLaw` reuses `blaw_split`, `pmean`, and `samp_mean` for the shared
answer list. `JointNextBound` reuses the existing `chainB` theorem for an
arbitrary adaptive continuation. Its fixed-completion error bound remains
an explicit premise for every answer list of the computed length. These
theorems do not turn that premise into an R1 classifier bound by themselves.

## Remaining obligations

The later [joint-decoder connection](JOINT-DECODER-BRIDGE.md) now recovers
C1 and this component from the queried address and earlier table, checks the
query/following labels and payload encodings, and preserves both messages.
Assembly of the generic protocol's full typed prefix, the complete round-wise
decoder, injection/density and R1 D1/D2/D3 instantiation remain open.
Pending-prefix composition at the initializer, ordinary and reseeded round
cases must also be included in that complete instance.

The concrete byte codec, Rust/committed-word/account correspondence,
settlement guards, universal masking/simulator argument and final private
spend theorem remain open. The generic `Qtot * maxErr` factor and charged
collision terms are retained; no grinding or work-normalization credit is
introduced. No Rust source or CU result changed in this step.

## Verification

Source base: `f9183a8c38df9e2ab63a5b2688006e6c6ba2b898`.
Eleven final focused targets passed on the pinned NUC. The combined
`R1JointPrefixCheckpoint-a` passed in 1.47 seconds at 3,532,168 KiB peak RSS
with zero swap, in a 4G/6G/0 high/max/swap scope. All 22 checkpoint axiom
reports contain only `propext`, `Classical.choice`, and/or `Quot.sound`.

Checkpoint source SHA-256:
`010cb15f5c8fdf2d452e9a602cc7dd496e0a56070bc80742260dd89949ac147d`.
The [evidence bundle](evidence/lean-joint-prefix-20261014/README.md) retains
exact attempt sources, failures, receipts, resource logs, runner settings
and final compiled objects. No unchanged full regression was rerun.
