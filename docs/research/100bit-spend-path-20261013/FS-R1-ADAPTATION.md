# R1 Fiat–Shamir adaptation: exact reuse boundaries

This is a root-owned implementation plan and dependency audit at base
`e8b1a73c6e3fd764ca01701c9c936cd705ce74b1`, not a Fiat–Shamir theorem.
The generic FS2 first-read framework and per-round sampler interface remain
reusable. The old concrete masked instance is not the actual R1 protocol.

The later [unified sampler connection](UNIFIED-SAMPLER-BRIDGE.md) gives one
definition for the 33-row schedule and proves the selected query-state
continuation into rho. The complete decoder/classifier instance and source
correspondence are still open; this does not apply the old concrete theorem
by changing its round count.

The subsequent [unified decoder connection](UNIFIED-DECODER-BRIDGE.md)
connects completed records to that run and gives a guarded row-32 component
in the old `R0C.V3.Dec` interface. This does not yet supply the component's
whole-trace injection or the full decoder/classifier instance.

## Facts that prevent a round-count-only substitution

1. R1 has 33 challenge rows. Its q22 sampler is row 31 and rho is row 32.
   `MaskProtocol.combinedSamplerAt last` uses a single squeeze before `last`
   and q22 at/after it. `MaskDuplexDecoder.combinedNsteps rounds i` likewise
   assigns eight pairs only at the final row. Instantiating those definitions
   at 33 would place q22 at the wrong row.
2. The old backward `Duplex.walk`, records and `completeRounds` model one
   advance per earlier round. With rho after q22, the decoder must recover
   an earlier multi-pair query round, including all its squeezed blocks.
3. R1 computes all eight query pairs, but `queries_from_pairs` resumes from
   the advance where the bounded scan stops. That may precede the eighth
   advance. `Q22.scanOut` and `DQ.out4` already model this selected state.
   The old q22 law must not be silently changed to an eighth-state law.
4. The R1 row-25 payload includes 87 point claims and 29 extra claims.
   The old typed context carries the extra vector from the start. The new
   message model must bind the actual later payload. A byte encoder cannot
   silently drop adaptive fields while retaining an injectivity premise.
5. Row 27 transmits only the 29 y1 values. The other opening claims belong
   to earlier messages; a synthesized algebraic opening view must preserve
   that chronology without pretending it was all transmitted at row 27.
6. `Transcript::new` hashes the P3 domain, variant and semantic state at
   the semantic/opening boundary. The current generic direct-duplex walk
   does not account for that extra hash edge. Initial public/C1 binding is
   also outside the challenge-row table. Source correspondence must include
   both operations and their oracle-read accounting.

The ten central Rust source hashes from `TRANSCRIPT-R1-INVENTORY.md` were
rechecked unchanged at the preceding base. The inventory describes the
unproved cost probe; no protocol or runtime source was changed here.

## Reuse without a future-message premise

`SemanticContext.withExtra` changes only the legacy context's extra vector.
The C2 word construction and `semanticBadZ` are definitionally unchanged.
`SemanticContextPrefix.no_hitFrom_withExtra_iff` reuses the existing indexed
prefix characterization to prove that the entire parsed prefix no-hit event
(up to 25 rows) is unchanged. Thus a fixed placeholder can be used for these
early classifiers. This result does not identify the old opening decision
with R1's decision, and does not by itself establish a causal oracle law.

## Recovery route under review

Preserve the actual selected-state q22 behavior. Reuse the old no-collision
lemmas to recover unique advance predecessors; recover the query absorb
boundary by following those predecessors. Recover only the advance path that ends at the selected state. An adversary
can first-read the rho absorb after obtaining that state and before reading
the unused query-chain tail, so the complete eight-pair spine need not be
in that first-read table. A prefix-completion record must enumerate the
missing squeeze cells on the recovered path and reconstruct the q22 result
from a truncated `scanOut`. Equality to the actual full result needs a
separate stopping/truncation lemma under the state-distinctness condition.

At `52023cce5`, the focused lemmas established only deterministic pieces: advance
rewinding under the existing no-collision/table premises, and membership of
the selected query state among the eight advances. At that checkpoint, the full decoder still needed to discover the correct
boundary, handle the domain-transition edge,
complete missing cells with the correct law, and satisfy the generic
first-read/injection obligations. In particular, state membership alone is
not a decoder or an independence theorem.

After that, the actual message parser, the R1 per-round bad events and
D1/D2/D3 composition remain to be instantiated. The current algebraic
candidate and input/output-state extraction can supply the deterministic
semantic endpoint. Authenticated-word/source correspondence, account guards,
shared-oracle collision accounting and privacy remain separate obligations.

## Checked increment

The following six focused targets are green:

| Target | Exact contribution |
| --- | --- |
| `R1SemanticContext` | Replacing only `extraClaims` preserves C2 words and the semantic classifier. |
| `R1SemanticContextPrefix` | The parsed first-25-row no-hit event is invariant under that replacement. |
| `R1DuplexRewind` | Unique advance-predecessor lookup and finite rewinding, derived from the old collision/table lemmas. |
| `R1QueryContinuation` | The actual selected state belongs to the eight advances, including early stopping. |
| `R1QueryRecovery` | Some selected index below eight has a correctly recovered predecessor path under the unchanged collision/table premises. |
| `R1FSReuseCheckpoint` | Combined import and ten axiom audits. |

The combined checkpoint passed in 1.37 seconds at 3,557,136 KiB peak RSS,
zero swap. All ten axiom reports use only `propext`, `Classical.choice`
and/or `Quot.sound`. This check composes the deterministic lemmas; it does
not yet instantiate a probability theorem or discover a decoder boundary.
Each target ran on the pinned NUC with 4G/6G/0 high/max/swap caps. Source,
failed attempts, receipts and compiled objects are retained in
[evidence/lean-fs-reuse-20261014](evidence/lean-fs-reuse-20261014/README.md).

## Hash-edge reuse inventory for the next step

Root inspected the older generic `UniformFrameCollision` and
`CausalInjectiveFrameBound` modules after a read-only inventory. They accept
an arbitrary injective state-to-address frame, and the causal theorem
allows the frame and prior-read list to depend on the preceding tape
prefix. They do not permit dependence on the current or future tape cell,
and do not instantiate the R1 source callback.

The concrete `FS2.Duplex.badColl` instead checks equality with a fixed IV,
earlier outputs, and the first 32 bytes of earlier/current addresses.
`Params.iv` is a value, not a function of the oracle. The R1 public/C1
initialization query and the reseed query with its trailing state bytes
therefore require explicit modeling and an appropriate causal frame
connection. Neither is supplied by setting `iv` to a hash expression in an
otherwise unchanged fixed-IV theorem. The generic frame results are reuse
candidates, with their source and first-read premises still to be proved.

All 14 Rust source/manifest fingerprints in the source inventory were
independently rechecked unchanged during the root audit. No source or CU
claim is inferred from these Lean structural checks.

## First-read table correction (after `52023cce5`)

The verifier's full eight-pair execution order does not force an adversary's
first rho absorb query to occur after all eight advances. The committed
`QueryRecovery.selected_path_recovered` remains a valid deterministic
statement with its explicit eight-cell premises, but those premises must
not be silently assumed for a first-read completing decoder. The checked
[first-read bridge](QUERY-FIRST-READ-BRIDGE.md) now locates the nearest
absorb boundary from the selected state, derives the required predecessor
path from the earlier table, and proves exact scan-prefix equality. Its
completion wrapper needs coherence only on its computed finite missing
list. No probability estimate or protocol source changed. The completion
sampler law and full transcript instance remain separate obligations.

## Background completion law

The [completion-law bridge](QUERY-COMPLETION-LAW.md) proves the exact
independent-answer law for the new query recovery component followed by
a single duplex round. It reuses the old answer-list lookup, background
mean splitting, and fresh sampler law. Actual oracle answers yield the
actual query result under the first-read theorem's existing premises.
The remaining probability connection is trace following/injection plus
the full prefix and R1 D1/D2/D3 instance; an independent-answer calculation
alone is not a bound for the adversarial source execution.

The next local trace-following connection and exact reusable interfaces are
recorded in [QUERY-INJECTION-NEXT.md](QUERY-INJECTION-NEXT.md).

## Local trace-following connection

[QUERY-TRACE-BRIDGE.md](QUERY-TRACE-BRIDGE.md) closes the local q22-to-next-
round trace-following obligation under the unchanged whole-trace collision
and read premises. An address/table decoder now returns the actual query
component and following challenge. The old `chainB` and 21-root results
also supply the local adaptive accepted-miss bound under explicit sampler
and fixed-data premises. The full earlier prefix and hash edges are not
part of this component; the complete R1 instance remains open.

## Opening-domain edge: checked local route

[RESEED-EDGE-BRIDGE.md](RESEED-EDGE-BRIDGE.md) now supplies a checked local
route for the source's trailing-state domain hash. It adds the parsed-state
collision event explicitly and recovers the reseed/predecessor from the
table before gamma's absorb. A sampler ending row 26 with the reseed has
the same challenge law as the older ordinary duplex sampler, and its local
trace following is checked. This retains the current hash-input bytes.

The complete earlier-prefix reconstruction must validate the recovered
domain frame and replace row 26's carried state by the reseed output.
Initial public/C1 hashing and the complete R1 instance remain separate
obligations; the local components are not a full `Inj3` proof.

## Initialization and ordinary prefix: checked local route

[INITIAL-EDGE-BRIDGE.md](INITIAL-EDGE-BRIDGE.md) adds the initializer query
explicitly to the row-zero sampler. A strict parser checks the literal
public prefix and recovers C1 from the queried address. The old `bfollow_ok`
and sampler-law theorems prove local trace following and the independent
completion law. `Params.iv` is not replaced by an oracle-dependent value.

An ordinary-prefix decoder now stops at the parsed initializer. Old
output-uniqueness and first-read-order lemmas derive its predecessor lookups
from the table before the next absorb. The exact ordinary records and C1
are returned under explicit whole-trace, chain and collision premises.
The opening-domain decoder now checks its complete fixed domain/tag frame.

These additions close the local initialization and strict frame duties,
while complete typed-prefix reconstruction, missing-answer completion across
the reseed and query boundaries, and the R1 generic theorem instance still
need composition. Rust/account correspondence and privacy remain open.

## Crossing the domain transition and completing ordinary prefixes

[OPENING-PREFIX-BRIDGE.md](OPENING-PREFIX-BRIDGE.md) now combines the strict
domain decoder with both ordinary record segments. Whole-trace first-read
ordering supplies every required earlier table cell. The recovered last
semantic record carries the reseed output, while its absorbed state and
payload remain unchanged. Label/offset checking connects the raw list to
the abstract message codec and the old `completeRounds` representation.

Actual answers on the computed missing squeeze list recover the expected
challenge sequence. The independent-answer law for that prefix followed
by a fresh ordinary round reuses the old background split and `samp_mean`.
It does not yet supply the full pending-list freshness, trace following or
q22/rho composition required by `Inj3` and the adaptive density instance.
The concrete byte codec, full source/account correspondence and privacy
remain separate.

## Shared completion of the ordinary prefix and q22

[JOINT-PREFIX-BRIDGE.md](JOINT-PREFIX-BRIDGE.md) extends recovery to the
table before the round following q22. The query absorb is proved to precede
that round; the ordinary records are recovered at the later table and their
known-state facts are derived from the explicit chains. One deduplicated
missing-answer list completes both ordinary rounds and q22, so a shared
hash address cannot receive two independent answers.

The combined trace-following theorem now returns the actual ordinary prefix,
query address/result and following challenge. The background law and adaptive
continuation bound reuse the old `blaw_split`, `samp_mean` and `chainB` results
with an explicit fixed-completion bound. This closes this component's
pending-list and trace composition, not the complete generic theorem
instance. Query/following-message binding in the address-only typed decoder,
all other round cases, R1 D1/D2/D3, source refinement and privacy remain open.

## Address/table component decoder and canonical final messages

[JOINT-DECODER-BRIDGE.md](JOINT-DECODER-BRIDGE.md) supplies the address/table
decoder for the combined component. Successful parsing exposes the recovered
C1 and ordinary records, expected query/following labels, and equality between
the decoded messages' encodings and the hashed payloads. The trace theorem
derives this successful parse from the explicit chains and returns the actual
messages and challenges. The decoder's adaptive continuation bound retains
the fixed-completion premise. The local rho bound now allows residual data to
depend on all earlier completed rounds as well as q22, while remaining fixed
before rho.

The new transcript view keeps C1 as the prover's first message and tags query
challenge values separately. Its list lift still needs the fixed row-zero
sampler/byte connection and the complete 33-round protocol definition. It is
not legitimate to make C1 part of the fixed public statement merely to reuse
the old protocol type. Full round dispatch, D1/D2/D3, source correspondence
and privacy remain open.
