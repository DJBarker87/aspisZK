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

## `FSV8AlignedAlphaTotalTape.lean`

- exit status: 0
- wall time: 2.71 s
- maximum RSS (`/usr/bin/time -v`): 6,778,476 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- source SHA-256: `04a1e66397cf170f2472a94f7b3c31b8db933e96e3f5d1ae5105bfab0f0eb3ae`

Starting from an actual `SuccessfulAlignedChallenge`, this deterministic leaf
constructs a four-output/four-advance `RelationAlphaTotalTape`.  Its output
prefix is the literal rejected-block sequence plus the accepted final output;
its advance prefix contains the matching actual advance answers in chronology;
both sides are padded only after the used prefix.  The four-block word bridge
is retained explicitly, and the padded output raw stream succeeds with the
same returned alpha.

The general consumer theorem `successfulTotalTape_of_output_prefix` further
shows that **any** `RelationAlphaTotalTape` whose output-side prefix through
the successful run's actual block count is equal to those source blocks has
`relationAlphaTotalSucceeds` and decodes to the same alpha.  Its four advance
coordinates and unused output suffix are arbitrary.  This removes any need
for the eventual router-realization proof to identify unused coordinates with
the leaf's zero padding.

This does not yet prove that the constructed tape is definitionally the named
coordinate pair produced by `alpha0SamplerCoordinates` for an exact-root
master tape.  That remaining source/router equality needs the exact root's
starting cursor and the slot-router execution to be connected to this same
`SuccessfulAlignedChallenge`; it cannot be inferred merely from the common
four-pair type.

## Public Rust sampler source tests

Command:

```text
/usr/bin/time -lp cargo test -p aspis-core --test v8_sampler_source_tests
```

- host: local macOS development machine
- profile: focused Cargo test profile (unoptimized; these are bounded
  control-flow tests, not a substantive arithmetic benchmark)
- exit status: 0
- wall time: 6.54 s, including a cold partial dependency compile
- maximum RSS (`/usr/bin/time -lp`): 633,257,984 bytes
- swaps: 0
- tests: 8 passed; 0 failed
- source SHA-256:
  `065519e4484ad33a637603faafbf068a099d980e1a39fa3ca9340f7e5709805c`

The tests call the public `Transcript::challenge_qm31` implementation with a
scripted memoizing hash oracle.  They check that ordinary alpha accepts zero,
masks high bits before canonical rejection, rejects the M31 sentinel rather
than folding it to zero, consumes the last buffered word without an extra
squeeze, permits all four limbs to use their eight-word retry bounds, advances
after first-limb exhaustion, uses distinct literal output/advance keys, and
reuses cached oracle answers after prequeries or repeated states.

No production source or protocol constant changed.  This is source-level
control-flow evidence only: scripted answers do not prove that actual oracle
coordinates are fresh or uniform, do not establish the random-oracle coupling,
and do not execute the complete selected V8 verifier.

## `FSV8AlphaRouterRealization.lean`

- exit status: 0
- wall time: 3.12 s
- maximum RSS (`/usr/bin/time -v`): 6,824,256 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- source SHA-256:
  `ceb8d386afc64cf1190114509f07a59493ecba76e1a5c91cb4e6373c246ce38c`

This leaf proves that every named output or advance slot in a chronological
labelled trace from the exact-root exposure cursor is the corresponding
literal component of `alpha0SamplerCoordinates`.  It preserves the router's
actual unused coordinates and does not replace them with zero padding.

The theorem consumes an `Alpha0RootLabeledTrace` package.  Construction of
that package from the same accepted exact-root execution remains open; the
package is not counted as source closure.

## `FSV8AlphaTableHistoryCoverage.lean`

- exit status: 0
- wall time: 3.17 s
- maximum RSS (`/usr/bin/time -v`): 6,842,484 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- source SHA-256:
  `420ee5cbcb0dccd56a4af9492f2ddb4c342dd157d6cef19413f1843a78370cdc`

This leaf constructs actor-agnostic table/history coverage from the actual
projected adversary run at `emptyOracle` and proves preservation through the
selected source/gamma and pre-alpha programs and through each aligned squeeze
pair.  A later cached call following a fresh advance is routed to a target
already available at the fresh advance request, rather than treating the
future cache lookup as an independent answer.

It does not yet place that target into the same exact-root global target event.
That native request/root-trace composition is the next source obligation.

## `FSV8AlphaFreshCreatorCoverage.lean`

- exit status: 0
- wall time: 2.87 s
- maximum RSS (`/usr/bin/time -v`): 6,842,112 KiB
- swaps: 0
- axioms: `propext`, `Classical.choice`, `Quot.sound`
- source SHA-256:
  `e58239537c73d950de33e2f5753259b828d0b4fe327accc279f687f98950d372`
- compiled artifact SHA-256:
  `39320a7e1da903ef2367c0dcababa8fb757e0722eda753889e0ddd1617dd8446`

This strengthens table/history coverage to a literal `.fresh` creator record
for every cached table entry.  The invariant is constructed from the
empty-oracle projected adversary root and preserved through the exact
source/gamma and pre-alpha programs and every aligned alpha pair/path.

This is the source fact needed by `RootVerifierNativeRequest`, whose prior
request branch retains fresh verifier records rather than arbitrary cached
records.  The separate theorem placing the creator's request into the same
exact-root target event is still pending.
