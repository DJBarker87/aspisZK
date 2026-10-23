# S6 complete accepted afterstate field provenance — 2026-10-23

## Exact enclosing claim

`AspisS6SourceCodec.AfterstateFactored.Frames.source_accepted_frames` states:

```lean
∀ (bytes : Slice U8) (afterstate : PoolV1PairVerifiedAfterstateV1),
  decode_pool_v1_pair_verified_afterstate_v1 bytes =
    ok (core.result.Result.Ok afterstate) → full_frame bytes afterstate
```

The sole premise is the complete actual decoder's accepted return. `full_frame`
retains all native afterstate fields and establishes all of the following on
that same byte slice:

- Exact 688-byte length and all header fields, including the success code.
- Actual root digest encoder returns the bytes at 16..48.
- Actual digest encoders for all twenty returned frontier entries reproduce
  their ordered 32-byte frames starting at byte 48.
- Actual U64 little-endian encoding of the returned next index is bytes 8..16.
- The complete actual afterstate validator returns Rust `Ok ()`.

This is ACCEPTED-ONLY field provenance, paired with the independently checked
TOTAL decoder in `S6-AFTERSTATE-DECODER-TOTALITY-20261023.md`. No independent
canonicality, input length, validation, child encoder success, or callback
correspondence is assumed. It is stronger than the prior totality-only decoder
contract but is not yet the accepted encoder inverse.

The five continuation proofs compose using a symbolic list-prefix lemma. Each
new digest frame is derived from the actual source read, exact conversion,
branch, concrete map_err and canonical digest decode; existing checked digest
inverses are imported. The root proof composes the full returned native record
and derives the source header guards. The complete decoder identity from the
previous packet transports the result back to the original complete extracted
function, preserving its Result semantics.

## Validation and trust boundaries

No Rust or production verifier source changed. Source freeze/compatibility,
reference transformations and release transport obligations are unchanged from
the totality packet. No per-call SDK or opaque serializer axiom was introduced.
Eight focused targets compiled in dependency order with the atomic local lock,
Lean 4.32.0, `-j1 -M4400`, warm dependencies, exit 0 and zero swap. All eight
axioms audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

| Target | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|
| `S6AfterstateDecoderFramesV1` | 27.332 | 2170798080 | 0 |
| `S6AfterstateFramePrependV1` | 24.149 | 2186788864 | 0 |
| `S6SourceAfterstateDecodedFramesV1` | 7.655 | 2285240320 | 0 |
| `S6SourceAfterstateAcceptedFramesV1` | 8.476 | 2237808640 | 0 |
| `S6AfterstateDecoderPart12FramesV1` | 5.641 | 2244640768 | 0 |
| `S6AfterstateDecoderPart8FramesV1` | 17.250 | 2249818112 | 0 |
| `S6AfterstateDecoderPart4FramesV1` | 5.465 | 2233991168 | 0 |
| `S6AfterstateDecoderPart0FramesV1` | 8.052 | 2280488960 | 0 |

Exact sources, commands, tool/source/import pins, revision, statuses and metrics
are recorded in the attempts selected by `s6-afterstate-accepted-frames-targets.json`.
Transitive object hashes are in `s6-afterstate-accepted-frames-import-pins.json`;
no compiled objects are included. The audit tool
`check-afterstate-accepted-frames.py` checks these receipts without replay.
Earlier failed continuation/header proofs remain excluded diagnostics, with no
installed `sorryAx` target. No resource options were raised and no unchanged
full replay ran.

## Remaining

Compose these exact decoded frames with the existing S2K native afterstate
encoder bytes theorem, respecting its native type/source pins, to establish the
688-byte inverse. Snapshot800, transition1520 and forest1880 inverses/composition
remain, as do the actual current full serializer/runtime/SDK and first-decoded
call-site ports. S1 preparation and resumed-powers caller ports remain open.
S2 is externally owned. The overall 100-bit target is not established.
