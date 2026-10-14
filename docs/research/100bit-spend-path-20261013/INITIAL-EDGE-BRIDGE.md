# Initial public/commitment hash and ordinary prefix recovery

The initialization hash is now an explicit sampler query. Its input contains
the fixed public bytes and the C1 commitment root; a strict parser recovers
the root from that input. This reuses the older background-sampler and
first-read machinery without setting a fixed IV to an oracle-dependent value.
The complete R1 Fiat–Shamir instance remains open.

## Checked local construction

`PublicInitFrame` models the literal P3 semantic initialization input:

```
38-byte domain || 0 || public length (four little-endian bytes)
  || public bytes || C1 root (32 bytes)
```

`PublicInitParse` requires the public length to fit in a u32, checks the
entire supplied public prefix, and requires exactly 32 trailing bytes.
`PrefixedStateCodec.parse_sound` proves that every accepted address has
exactly that frame. Constructor round trips alone would not establish this.
These are byte-list model theorems; the Rust integer/serialization refinement
and typed-public correspondence remain separate.

The row-zero message is the five-byte empty record, absorbed with label 160.
`InitialSamplerLaw` explicitly performs initialization, row-zero absorption,
squeeze and advance. Its independent-answer law reduces to the same fresh
squeeze/advance mean used by the existing ordinary sampler. The C1 root is
fixed by the queried address before this completion law is applied.

`InitialTrace.follows` derives freshness, distinctness and necessary read
order from the old whole-trace collision complement and actual read facts.
It applies the existing `bfollow_ok` theorem. `InitialDecoder` then returns
the actual C1 root and row-zero challenge/state, using only the fixed public
bytes, the queried address and the table available at its first read.
`BackgroundOutputMap` supplies the pure output-map identity used to retain
the recovered C1 root. No oracle is an input to the decoder.

## Reconstructing the preceding ordinary records

`InitialWalk` walks backward through unique advance and absorb predecessors.
At each step it checks whether the predecessor's hash input is the strict
initialization frame. It returns the recovered C1 root and the records in
their original order. It does not need an oracle-dependent stopping state.

`InitialWalkCells` derives its lookup premises from consistent table cells
and the old no-collision event, reusing `DuplexRewind.unique_advance` and
`ReseedBoundary.findCell_correct`. An intermediate advance address cannot
be mistaken for initialization: it has 33 bytes, whereas the initialization
frame has at least 75. `PublicInitBoundaryFacts` proves this separation.

`DuplexRecordPrefix` derives the required absorb/advance ordering and table
cells from whole-trace read facts and the existing first-read collision
lemma. `InitialWalkTrace.walk_before_next` applies both connections: the
actual prefix is recovered from the table before the following address is
first queried, provided that address begins with the actual endpoint state.
No successful-lookup or already-present-prefix assumption remains in this
theorem. The read facts, chain equations, public-frame bounds and collision
complement remain explicit; they still need the full protocol instance.

## Strict opening-domain recovery

`StrictReseedDecoder` applies the same prefix parser to the literal P3
opening domain and fixed variant tag. Accepted inputs have exactly that
prefix and one trailing state. `StrictReseedTrace` strengthens the preceding
[reseed bridge](RESEED-EDGE-BRIDGE.md): the actual strict decoder succeeds
before the next absorb, under the same explicitly charged collision events.
This closes the local frame-validation duty left open in that bridge.

## Limits and next connection

An ordinary-record walk returns raw labels and payloads. The complete R1
decoder must still validate the typed row sequence, reconstruct every
challenge including missing squeeze answers, cross the reseed edge with the
chosen row-26 state convention, and compose the q22 selected-prefix component.
It must then discharge the generic injection, density, chain/read and
D1/D2/D3 obligations. A correct local decoder is not that complete instance.

The source-only inventory compares the literal domain, field order, public
sizes, empty record and label with current Rust. Private-transfer public
bytes have length 1455 and withdrawal public bytes 1427, so their initializer
inputs have lengths 1530 and 1502 respectively. Those observations do not
prove Rust execution correspondence or account authorization.

The generic oracle-query factor and charged collision terms remain in the
security accounting. Nothing here supplies work/grinding credit, establishes
the full privacy simulator, or claims a completed 100-bit private spend.

## Verification

Source base: `eb1b410e87539f4840de396b98af04f50d54f184`.
Fifteen final focused targets passed. The combined `R1InitialCheckpoint-a`
imports this connection and the preceding reseed/query checkpoint; it passed
in 1.41 seconds, at 3,529,016 KiB peak RSS, with zero swap in a 4G/6G/0
high/max/swap scope. All 33 axiom reports contain only `propext`,
`Classical.choice`, and/or `Quot.sound` (or no axioms).

Checkpoint source SHA-256:
`ff07ec7b9d1bd9699314372fcf8c4e9b0a1f135b2ff57ba80ca96b76a8fdec57`.
Focused NUC receipts, all failed attempts, exact source snapshots, runner
configuration and compiled objects are in
[the evidence bundle](evidence/lean-initial-edge-20261014/README.md).
No Rust source changed and no unchanged runtime regression was rerun.
