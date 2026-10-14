# Reusing the query-chain proof for unified row 31

The completing decoder for query row 31 now returns the exact prefix,
message, and challenge of the unified prover/verifier experiment. Together
with the previously checked initial, semantic, reseed, opening, and rho
cases, this supplies individual decoder-case theorems for all 33 rounds.
It does not yet supply one correctly dispatched decoder, `Inj3`, or the
complete security theorem.

## What is reused

`QueryBackgroundChain` generalizes the structural bookkeeping from the old
`DQ.chainBS` to the existing generic duplex parameters. Its event-membership,
output, order, and distinctness lemmas retain explicit premises. The old
`bfollow_ok`, trace-suffix order transfer, collision consequences, and prefix
completion proofs are applied unchanged.

The query sampler computes eight squeeze/advance pairs. Its background
representation spawns each squeeze request and asks for the corresponding
advance; it does not assume an adversary read the squeeze before the advance.
The advance states are retained as a list. The output runs the existing
`Q22.scanOut` on the squeezed answers and that list, preserving both failure
and the scan's selected continuation state. It does not replace the selected
state with the eighth advance.

`QueryChainTraceFacts` derives root and inter-step order, distinct states,
and separation from earlier known states under the existing collision
exclusion. `PrefixQueryTrace` uses those facts to discharge freshness,
distinctness, and order for the old background-follow theorem. Missing prefix
squeezes remain explicit pending reads, with no assumption that they were all
available before the query absorb.

`QueryBackgroundLaw` generalizes the old chain averaging identity and proves
the matching independent-answer law for `QuerySampler.chain`.
`UnifiedQueryLaw.background_sampler_law` places prefix completion outside the
query sampler average. Its bound-transfer theorem still requires an explicit
fixed-prefix bound; it is not a numerical soundness theorem.

## The new connections

`UnifiedQueryDecoder` reuses `UnifiedOpeningDecoder.parse`, guards the recovered
record length at 31, and supplies the eight-pair completing sampler.
`UnifiedQueryView` identifies its completed output with the actual run.
`UnifiedQueryInjection` derives the parse and pending-read facts from
`UnifiedOpeningRecovery.recover_before_row` at the query boundary, and then
applies `PrefixQueryTrace`. `UnifiedQueryCase` translates this to the actual
prover/verifier experiment and the protocol's first-cell interface.

These results retain the public length and row-zero codec premises, the
first-read budget, and both explicit collision exclusions. They do not
assume successful verification or the desired decoded output.

Two generic adapters prepare the existing state-valued decoders for the same
list-valued interface: `BackgroundOwnMap` maps a sampler's result while
preserving follow and law behavior, and `DecoderStateList` applies the singleton
map to a decoder. No extra sampling step or probability loss is introduced by
this representation change.

## Dispatch facts and next obligations

The inspected Rust formula is `[0, 0xa0 + row]` in both the semantic and
opening transcripts. `UnifiedLabels` models the second byte and proves
injectivity and row recovery for indices below 33. It does not yet connect
that definition to an arbitrary parameter's `p.lbl` or prove Rust semantics.
`PublicInitAbsorbSeparation` proves that a successfully parsed initialization
frame cannot parse as an absorb frame: byte 32 of the fixed initialization
domain is 84, while absorb parsing requires zero there.

The next decoder step is to dispatch initialization separately and use the
unique absorb label for the remaining cases. This is a proposed composition,
not an implemented theorem in this batch. The row-zero codec hypotheses also
need to be justified for the concrete proof representation; the present
conditional case statements do not silently discharge them for every prover.

The full D1/D2/D3 and numerical instance, cryptographic/source correspondence,
account and settlement refinement, universal mask rank, and complete privacy
simulation remain separate obligations. No runtime source or CU claim changes
in this batch.

## Focused verification

Base revision: `ff314073cab76662de4e5711cdda5542c8bcfb62`.
The [sealed evidence](evidence/lean-unified-query-20261014/README.md) records
14 final targets, 38 attempts (23 failed, one superseded success, 14 final),
all source snapshots, receipts, and a deterministic object archive. Failed
attempts are retained as failed evidence, not accepted proofs.

The combined `R1UnifiedQueryCheckpoint-a` passed in 1.40 seconds, peak RSS
3,530,000 KiB, zero swap, with 39 axiom reports using only `propext`,
`Classical.choice`, `Quot.sound`, or no axioms. Every compile used the pinned
NUC workspace with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and the
5,000 MiB Lean threshold. Root inspected the statements and proof routes,
checked the dependent targets, verified attempt/resource/source/object hashes,
and confirmed all 14 central runtime fingerprints remain unchanged.
