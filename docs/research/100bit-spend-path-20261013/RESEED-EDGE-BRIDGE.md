# Accounting for the P3 opening-domain hash

The local opening-domain hash connection now compiles without changing the
Rust transcript or its hash-input bytes. This extends the earlier
[query trace bridge](QUERY-TRACE-BRIDGE.md). It does not instantiate the
complete R1 Fiat–Shamir theorem.

## Root-selected model

The source computes a semantic row-26 absorb, squeeze and advance, followed
by `H(P3_domain || variant_tag || semantic_state)` before the row-27 gamma
absorb. Model that last hash as the end of row 26: its challenge value remains
z1, while its carried continuation state becomes the reseed output. Row 27
then starts at its actual message-dependent absorb. Its first entry point
is not moved to the earlier reseed query, which does not contain y1.

This is a choice of mathematical round boundary. It does not move a Rust
operation, remove its oracle query, change challenges, or assert that the
source executes four uninterrupted queries. The local trace theorem allows
other reads between those operations. The complete protocol's chain/read
instance remains to be assembled.

## Checked components

- `ParsedStateCollision` bounds the event that a fresh output equals the
  state parsed from the current or an earlier queried address. The parser
  is any fixed `Addr -> Option State`; no injectivity premise is required.
  There is at most one parsed candidate per address, so the density is at
  most `Qtot / 2^256` and the adaptive event costs at most
  `Qtot^2 / 2^256`.
- `ParsedStateTrace` adds that event to the unchanged older duplex event.
  Their union costs at most `3 * Qtot^2 / 2^256`, compared with the older
  `2 * Qtot^2 / 2^256`. Outside the added event, an address containing a
  parsed predecessor output must be first-read after that predecessor.
  The parser and its exceptional event are fixed before averaging over
  the oracle; no current-answer-dependent parser is admitted.
- `TrailingStateFrame` decodes the final 32 bytes of a prefix/state frame.
  `OpeningReseedFrame` specializes it to the literal 29-byte P3 domain,
  one variant byte and 32 state bytes. The frame is 62 bytes and binds both
  tag and state. The evidence records an independent literal comparison
  with `transcript.rs` and `transport.rs`; that is not Rust refinement.
- `ReseedBoundary.recover_before_next` proves that the predecessor cell
  and reseed cell are already in the table before the following absorb.
  A decoder using only that table and the endpoint state recovers the
  actual reseed address and predecessor state. It uses the new parsed-state
  ordering lemma and the existing output-uniqueness theorem.
- `ReseedTrace.follows` proves exact trace following for the four-read
  local sampler. Read facts, whole-trace consistency, a first-read bound,
  and the two collision complements are explicit. Address distinctness,
  freshness and order are derived, not supplied as desired conclusions.
  Its pending background list is empty; integration with all earlier
  missing squeeze cells is still a full-prefix duty.
- `ReseedSamplerLaw` checks the independent-answer law, including arbitrary
  pending background answers. `ReseedRound` defines the ordinary sampler,
  proves its exact four-address trace and output, and identifies its law
  with the existing ordinary duplex challenge law. The additional hash
  answer does not change that law.

The extra collision term is charged in full. These results neither add
work/grinding credit nor remove the generic `Qtot * maxErr` factor.

## Integration still required

The complete decoder must reconstruct every earlier message, validate the
recovered domain/variant frame, and carry the reseeded state at the row-26
boundary while preserving the semantic challenge value. The local
`ReseedBoundary.recover` returns the recovered address and its trailing
state; it is not by itself a strict domain validator or full prefix parser.

Public/C1 initialization remains a separate explicit hash edge. It cannot
be handled by silently setting the old fixed IV to an oracle-dependent
value. Row-0's empty message makes an explicit initializer-plus-row-0
sampler a possible next connection, but that sampler, public encoding,
and commitment parser are not established here.

The full `Inj3`, `ChainDensity3`, D1/D2/D3 and source/account/settlement
connections remain open, as does the actual-field privacy argument.
The existing 33-row schedule has not yet been instantiated merely by
proving these two local boundary components.

## Verification

Source base: `1268803b1b3ecab9120af3d32356542116dcf9a9`.
Nine final focused targets passed on the pinned NUC. The combined
`R1ReseedCheckpoint-a` imports this connection and the prior query bridge;
it passed in 1.42 seconds, 3,526,844 KiB peak RSS, zero swap, with 4G/6G/0
high/max/swap limits. Its 25 axiom reports contain only `propext`,
`Classical.choice`, and/or `Quot.sound`.

Checkpoint source SHA-256:
`61aed9076a02da2978d6385071eef1dc7e1c11ceb3cc9dbda019e59afdb40d74`.
The [evidence bundle](evidence/lean-reseed-edge-20261014/README.md) retains
failed attempts, the superseded unprefixed module build, exact source
snapshots, resource receipts, runner/environment, and final objects.
No Rust source changed, and no unchanged runtime suite was rerun.
