# S6 complete afterstate decoder totality — 2026-10-23

## Enclosing obligation closed

`AspisS6SourceCodec.AfterstateFactored.Total.source_total` proves:

```lean
∀ bytes : Slice U8, ∃ result,
  decode_pool_v1_pair_verified_afterstate_v1 bytes = ok result
```

This is TOTAL, not ACCEPTED-ONLY. Input length, header validity, canonicality,
child decoder success, and validator success are not hypotheses. All 21 digest
reads, next-index read, actual validator, original Rust error mapping, and full
native afterstate carrier are retained. Outer fail/div is excluded for every
input in this extracted function's semantics. Runtime allocation/SDK behavior is
not inferred from this pure Result statement.

The proof factors the unchanged extracted decoder into five four-frontier-field
continuations. `AfterstateFactored.decode_source` proves full Result equality
with the original complete decoder, including failures and every error. Kernel
proof unfolds only the factored continuations and compiler-generated match
helpers; it does not substitute simplified data carriers or opaque callees.
The generator also checks textual re-expansion of each original fragment.
Reached length 688 is internal to the continuation proofs; the enclosing theorem
has no input length premise. Concrete canonical digest and validator totality
proofs are reused, rather than assumed.

## Source and validation

No Rust or shipped verifier source changed. The source extraction and five
previous reference transformations remain as documented in
`S6-ENCODER-TOTALITY-20261023.md` and `S6-DIGEST-ACCEPTED-INVERSE-20261023.md`.
A refreshed compatibility audit checks every previously pinned statement-crate
file plus core field source against the observed research revision; see
`evidence/s126-current-caller-20261021/s6-statement-source-compatibility-20261023-latest.json`.
It does not re-pin the current verifier or release binaries.

All targets compiled individually in dependency order using the atomic local
lock, Lean 4.32.0, `-j1 -M4400`, and existing warm objects. No unchanged full
manifest replay ran. Exact source/tool/direct-import pins, revision, command,
exit status, wall time, RSS, swap and axioms are in each listed receipt.
The focused transitive object hash closure is
`s6-afterstate-decoder-total-import-pins.json`; binaries are not distributed.
All eight accepted targets exited 0, with 11 axioms reports containing only
`propext`, `Classical.choice`, and `Quot.sound`.

| Target | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|
| `S6AfterstateDecoderFactoredV1` | 4.553 | 2340306944 | 0 |
| `S6SourceAfterstateDecodeHelpersV1` | 3.438 | 2284355584 | 0 |
| `S6SourceAfterstateDecodeTotalV1` | 4.359 | 2279096320 | 0 |
| `S6AfterstateDecoderPart16TotalV1` | 7.691 | 2276737024 | 0 |
| `S6AfterstateDecoderPart12TotalV1` | 7.276 | 2272821248 | 0 |
| `S6AfterstateDecoderPart8TotalV1` | 3.137 | 2279718912 | 0 |
| `S6AfterstateDecoderPart4TotalV1` | 4.278 | 2271150080 | 0 |
| `S6AfterstateDecoderPart0TotalV1` | 10.288 | 2271657984 | 0 |

Earlier factoring attempts (v1–v11) are retained as excluded diagnostics. They
hit proof elaboration/matcher alignment issues; no failure was rerun with raised
resource options. The generator check additionally caught a JSON integer-key
comparison bug; its metadata now uses explicit string keys. This changed no Lean
source or theorem. Run `factor-afterstate-decoder.py --check` and
`check-afterstate-decode-total.py` for source/evidence audits without a replay.

## Remaining obligations

This removes the complete afterstate decoder's internal range/totality obligation.
It does not prove the 688-byte accepted encoder inverse. The 800-byte snapshot,
1,520-byte transition and complete 1,880-byte forest inverse/composition remain.
The actual current stage-1 public1880 serializer, decoded statement transport,
ordered runtime/SDK reads and effects, allocation/abort behavior and full caller
ports remain open, as do S1 preparation/caller source ports. The existing
S2K actual afterstate encoder byte theorem was located and must be reused with
its exact native type and source pins rather than reproved or attributed to a
new source by name. S2 remains externally owned. The 100-bit target is not yet
established.
