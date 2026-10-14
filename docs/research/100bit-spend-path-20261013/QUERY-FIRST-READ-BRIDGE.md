# Recovering the query round before rho's first read

This bridge extends the old duplex and q22 proofs to recover an earlier
query round from the oracle table preceding a following endpoint. The
endpoint may be rho's absorb address. It preserves the actual bounded
query scan and its selected continuation state.

## The first-read issue

R1 evaluates eight squeeze/advance pairs, but q22 can select an earlier
advance as its continuation state. An adversary can query rho's absorb
address after learning that selected state and before reading the unused
advance tail. Consequently, the decoder cannot assume that the complete
eight-pair path is in the table preceding rho's first read.

The earlier `QueryRecovery.selected_path_recovered` theorem is correct
with its explicit eight-cell table premise. This bridge removes that
premise from the first-read application rather than treating verifier
execution order as adversarial first-read order.

## What the new proof derives

`DuplexAbsorb` reuses the old collision lemmas to distinguish an absorb
output from an advance output and to recover its unique address. The
bounded `DuplexSeek.seek` follows unique advance predecessors until it
finds an absorb boundary. It does not receive a guessed stopping index.

`DuplexOrder` derives the strict first-read order of the advance chain and
distinctness of its advanced states from the existing collision event.
`DuplexPrefixTable` then proves that the absorb and the selected advance
prefix are in the table before the following endpoint. It assumes only
whole-execution reads and the endpoint's literal leading state bytes;
it does not require unused tail cells in that preceding table.

`QueryTruncation.scanOut_truncate` proves an exact result equality: if the
returned state is absent from an omitted suffix, scanning through the
selected prefix yields the same result as the full scan. Distinct advanced
states justify this condition at the selected index. This preserves both
the ordered query result (or failure) and the continuation state.

`QueryCompletion` fills the recovered path's squeeze values from the table
or supplied answers. `QueryFirstRead.recover_query_before_endpoint` joins
these facts. A nine-step search locates the absorb boundary for any of the
eight possible continuation advances. Completing the missing squeeze
cells consistently with the oracle recovers the full scan's exact result.
`QueryDecoder.recover_correct_on_missing` exposes this as a deterministic
query-round recovery function, without an existential index in its output.
Its coherence premise refers only to the finite, deduplicated missing-cell
list computed by the decoder; it does not demand answers at every absent
oracle address.

All old collision and trace-consistency premises remain explicit. The
whole trace must contain the absorb, all eight advance reads and the
following endpoint; the theorem derives which of those reads occurred
before that endpoint. Squeeze answers absent from the preceding table
are subject to an explicit oracle-coherence premise for this equality
result. That premise is not an independent-sampling law.

## Remaining integration

The full decoder still needs earlier-round records, the public/C1
initialization and the opening-domain hash transition, canonical message
parsing, and the completion sampler's distribution and injection laws.
The result here is a deterministic component under the old collision
event, not a new bound for the full R1 protocol. The R1 D1/D2/D3 instance,
Rust/account correspondence and complete privacy theorem remain open.

## Focused verification

The twelve focused final targets and their combined checkpoint passed on
the pinned NUC. `R1QueryFirstReadCheckpoint-b` took 0.74 seconds at
1,828,696 KiB peak RSS, with zero swap, under the 4G/6G/0 high/max/swap
cgroup limits. Its 28 axiom reports contain only `propext`,
`Classical.choice` and/or `Quot.sound`. No historical theorem, Rust
source, sampler, or security estimate was changed.

Exact attempt sources, failed attempts, receipts, source/object hashes and
the compiled-object archive are retained in
[evidence/lean-query-first-read-20261014](evidence/lean-query-first-read-20261014/README.md).
The source base is `52023cce56db49914ea5dc6980d859ec8786360d`; the
checkpoint source hash is
`dab401e2923b387417515845d1567bc5679147fae554d99cf14acfc867ba9af0`.
