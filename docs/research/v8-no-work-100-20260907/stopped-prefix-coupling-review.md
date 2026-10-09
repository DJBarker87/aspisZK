# Local stopped-prefix finite-tape coupling

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: **checked**. `StoppedPrefixCoupling` v3 passed the focused NUC check
with eight standard-only axiom audits. Sampler work was then frozen at the
user's priority change; the aggregation/ROM obligations below remain open.

`StoppedPrefixCoupling.lean` proves the first local coupling step,
not the full nested sampler law. For a fixed consumed block prefix `b` of
length `k`, its `PrefixFibre b n` contains exactly the length-`k+n` tapes
whose first `k` coordinates equal `b`. An explicit append/split equivalence
identifies this fibre with all length-`n` unread suffixes. Equality of finite
averages transports the uniform fibre measure to uniform unread suffixes.
No subset of suffixes is discarded or reweighted.

The source bridge starts with an **actual** successful ordinary decode.
Its consumed prefix is constructed using the decoder's proved `blocksUsed`
bound. Source locality then proves that every tape in the corresponding
prefix fibre has the same decoded record, except for the replaced unread
suffix. The original `decoded.remainingBlocks` is not conditioned on: doing
so would disclose the supposedly unread coins and invalidate this argument.

For at least four unread blocks, the next literal ordinary decoder's value
depends only on the first four. The proof treats both outcomes: a successful
call extends with its unchanged value; a hard failure remains a failure on
all extensions. The checked four-block decisiveness theorem excludes the
short-input/layout alternatives. Thus, in each consumed-prefix fibre,

    Pr[next literal ordinary value = t] = successMass/P⁴.

This averages the actual next decoder on the entire unread suffix. It does
not advance the source cursor by four, and it does not move leftover words
from the last consumed block into the next call.

Finally, the same coordinate decomposition is transported through
`NestedCircleRunRefinement.source_pair_refines`: running the literal source
on a fibre tape equals running the chronological controller from its state
after the fixed prefix, then on the unread suffix. No caller supplies a
source-output correspondence equation.

## Remaining aggregation and oracle obligations

The next step is a partition over variable-length stopped histories, proving
that histories reveal only their consumed prefixes and that all continuing
states have enough remaining tape. This local fibre result does not yet
establish the whole controller's `NestedCircleMass.Generic.Uniform` experiment
or a measure-preserving global adaptive slot router.

An explicit oracle table is unnecessary for this ideal independent finite
tape calculation. It becomes necessary, or must be replaced by an equivalent
proved lazy-oracle model, when relating actual hash inputs to fresh tape
coordinates: repeated inputs, adversarial prequeries, answer absorptions and
restarts cannot be justified by distinct labels. No ROM freshness, grinding
credit, FS advantage, or complete extraction theorem is claimed here.

Only current checked imports are used. The proof is symbolic in prefix and
suffix lengths; no finite-field or tape enumeration was performed.

## Focused evidence

All three attempts ran only this new leaf on the inherited pinned NUC
overlay, through Tailscale `100.108.41.90`. Preflight found 46,891,692,032
bytes available and no active compiler scope. Lean 4.32.0 used `-j1 -M9500`,
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPU 200%, recursion depth
200 and 250,000 heartbeats. Source parent `e969d9fa…` remains separate from
inherited runner research pin `289d7356…` and borrowed V7 pin `26a9cd47…`.

- `stopped-prefix-coupling-nuc-v1`: exit 1, 3.10s, peak RSS 6,815,668 KiB,
  zero swaps. A reserved binder name (`prefix`) caused a parser cascade.
- `stopped-prefix-coupling-nuc-v2`: exit 1, 8.02s, peak RSS 6,817,940 KiB,
  zero swaps. After the binder rename, only a multiline record-update parser
  error and an under-specified callback in the averaging rewrite remained.
- `stopped-prefix-coupling-nuc-v3`: exit 0, 3.39s, peak RSS 6,851,912 KiB,
  zero swaps. All eight audits are standard-only (`propext`, optionally
  `Classical.choice`, and `Quot.sound`), with no warnings. Both provenance
  checks passed all 887 entries and remained unchanged.

The fixes renamed code binders, placed the record-update value on one line,
and supplied the exact typed averaging callback. No mathematical premise,
resource limit, recursion limit or heartbeat limit changed. Every attempt's
exact source snapshot, log and manifest is retained under `experiments/`,
along with the green output.

Green source/snapshot SHA-256:
`de67e14d2c44dd4a08a3fde3929c636cd4cd1559cbca8b737bf836f0e1348708`.
Output:
`b531db9666ec52c58f1af27283b510fd43d234508643a06d3e06b7bad4c58fad`.
Manifest:
`9da1e728f5d2dbaa83fe7ba367f3a6d3309abbe266ac95469ba3bb8a26d63ffd`.
