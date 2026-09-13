# Fresh-cut pack: focused Lean leaves

Date: 2026-09-13

Scope: port and check the supplied literal buffered-decoder leaves and exact
bounded-rejection arithmetic.  This evidence does **not** establish that an
actual V8 oracle coordinate is fresh/uniform, does not cover cached source
cases, and does not invoke the first-block fallback.

Toolchain: Lean 4.32.0,
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, on the dedicated Linux NUC.
Each job used a user systemd unit with `MemoryHigh=7500M`, `MemoryMax=8G`, and
`MemorySwapMax=0`.

## `FSV8SourceBufferedDecode.lean`

- exit status: 0
- wall time: 0.31 s
- maximum RSS (`/usr/bin/time -v`): 773,788 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`; the all-sentinel theorem
  uses only `propext`
- source SHA-256: `e55e78b5c8ef5c7a9884d125d1713f52edf6b9fc2bee8a30bbade2a6baee1f0e`

Checked statements: a legal buffered sentinel prefix followed by a canonical
word decodes without squeezing; four such limbs decode from one buffered
stream; the corresponding literal first-output pattern determines the source
challenge; eight sentinels reject at the first limb.

## `FSV8ExactRejectionWeights.lean`

- exit status: 0
- wall time: 2.46 s
- maximum RSS (`/usr/bin/time -v`): 6,515,692 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- source SHA-256: `3b5f4019ff7440f5a087d3608c198f15d69ee8823ab302ca878e282659f4281c`

Checked statements: the bounded geometric identity; the one-limb per-value
mass partition and closed form; the four-limb success partition; fixed-tuple
mass equals total success mass divided by `(n-1)^4`; and the literal V8
`n=2^31`, cap-eight specialization.

The remaining source probability obligation is to connect this ideal IID
word-tape law to actual routed fresh coordinates at a causal V8 cut while
retaining output/advance cache cases.  No such premise is introduced by these
files.
