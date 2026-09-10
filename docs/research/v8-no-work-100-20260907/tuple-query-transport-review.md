# Fixed tuple to actual query transport

Status: all three focused leaves checked and frozen. Parent revision
`ed41b2537e7dad15ce8055d9e5524e337ee8b9a4`.

The new [core](experiments/TupleQueryTransportCore.lean),
[selected symbol bridge](experiments/TupleQuerySymbols.lean), and
[selected zero-check adapter](experiments/TupleQueryTransport.lean) remove a represented
adaptive quotient from the actual pointwise query residual. The fixed target
is a width29 tuple of natural1024 messages. It is quantified before gamma;
the quotient and final may depend on gamma and alpha. No claim is made that
an arbitrary final is represented by this tuple.

For a stored symbol `i`, the constructed polynomial is exactly
`OwnSymbolCollision.residual (received29 c1 c2) (expected tuple) i`, with
`expected tuple lane i = exactInitialEncoder (tuple lane) i`. Its degree is
at most28, and it is the zero polynomial precisely when every component
matches at that symbol. Pinned V7 encoder linearity identifies its evaluation
with `rawBatch_gamma(i) - encode(batch_gamma(tuple))(i)`.

At a nonpole, the checked image/reconstruction identity gives

`virtual_gamma(i) - encode(Q)(i) = residual_i(gamma) / L(i)`.

Here `original(Q) = batch_gamma(tuple)` is an equality of actual message
coefficients. The chord denominator is unchanged by `atGamma`; only the
batched interpolant changes. No polynomiality is assumed for the received
word, and Q is not frozen before alpha.

The actual query residual is **final minus received**. The generic core
proves the full value/sign identity underlying

`actualQueryResidual = -fibreFold(errors / L)(alpha)`.

The minus sign is necessary. The retained selected adapter proves only the
exact zero-check equivalence, not the failed full concrete value conversion.
Its premise is the literal `final = coefficientFoldLayer 256 alpha Q`.
The selected schedule uses
the actual `childIndex` and low-bit slot order
`(x,y), (x,-y), (-x,-y), (-x,y)`, including the negative second-pair
y-twiddle. The polynomial on the right is the one in the existing
[FixedTargetQuerySupport](experiments/FixedTargetQuerySupport.lean), not a
new abstract fold with an assumed correspondence. A nonzero residual at one
legal slot forces this polynomial to be nonzero and degree at most3.

`SelectedReceivedOracle` supplies the exact ordered-query and field-domain
index mapping. The zero-check adapter's oracle reference Q remains arbitrary:
no hidden reference-quotient equality is used. These are checked mathematical
source maps, not a new authenticated-byte/replay coupling.

Poles remain explicit. The adapter requires all four denominators to be
nonzero at each queried fibre. It does not assume global nonpoles, remove
poles from the original sampling domain, or resample rejected schedules.
The companion count must give schedules containing a pole zero accepted
mass, or separately account for those schedules. The old unguarded
fixed-target theorem's global denominator premise must not be silently
substituted for this local condition.

This leaf does not prove the high-agreement gamma exception, a family union,
the scalar rho/later repair bound, a sampler law, or payment extraction.
Those are separate consumers of this exact transport.

## Verification

The missing compatible FixedTargetQuerySupport output was restored by the
parent's separately recorded focused export of unchanged source. No laptop
compilation or package replay was used.

`TupleQueryTransportCore`, NUC attempt `tuple-query-transport-core-nuc-v1`:
exit0, wall3.05s, peak6,688,860KiB, swaps0. All four printed declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA256
`37157fbca7199ed1e7292c452f21e59be5de99aa0a7eedf683200c7c4e1b4027`;
olean SHA256
`8f857d3e4582a4551672120d348e4e3a531dfce062307a417466ef6ed95b65cb`.
The exact source snapshot, per-run manifest, log and olean are retained
locally. The core is frozen.

`TupleQuerySymbols`, NUC attempt `tuple-query-symbols-nuc-v1`: exit0,
wall3.75s, peak6,849,744KiB, swaps0; eight standard-only audits. Source
`1ad7a5486d940e92c820c4e88640b2535225add7b0a4303729ce024d712b79f9`;
olean
`71e24887e661aeefab1eeb5e235d5029cf4fbf063ebf5c1763011ce81c63639c`.
This file is frozen and retains the namespace `AspisV8.TupleQueryTransport`.
It exports the actual expected/errors/denominator/Legal definitions, degree
and own-support characterization, exact symbol transport, and nonzero-cubic
result. The same proofs had already passed inside failed larger attempts;
the split exports them independently instead of replaying them during every
remaining operation-conversion experiment.

The ten original `tuple-query-transport-nuc-vN` attempts are retained as
failed diagnostics, never as checked modules. V1–V3 localized deep selected
type conversions; explicit arguments and named constructor unfolding fixed
the symbol proofs. V4's full type trace identified Field-projection versus
direct QuadraticAlgebra subtraction/negation paths. V5–V6 tested explicit
local operation projections without resolving the full-value conversion.
V7–V9 were compact diagnostic attempts, including local-context/index errors;
their failures are retained. V10 tried two authorized declaration-local
`maxRecDepth400` static interfaces but hit the unchanged150,000-heartbeat
bound (and doc-comment placement diagnostics). That approach was abandoned:
no400 setting or local operation override remains in the retained core,
symbols, or current zero-check draft. No memory or heartbeat cap was raised.
All ten exact source snapshots, logs and per-run manifests are local.

V11 tested the new zero-check formulation: the two generic lemmas checked,
but a final concrete fold conversion remained (exit1,3.18s,
6,810,236KiB,swaps0). The successful replacement no longer identifies
alternate concrete expressions for inverse twiddles by reduction. Instead,
`Generic.fold_check_twiddles` accepts symbolic inverse scalars and proves
the required identity from `2*x*ix=1`, `2*y*iy=1`. The selected proof supplies
the literal canonical inverse arrays and the previously checked
`canonical_one_fold_schedule_exact`; no caller correspondence is assumed.

`TupleQueryTransport`, NUC attempt `tuple-query-transport-nuc-v12`: exit0,
wall3.51s, peak6,848,460KiB, swaps0; five standard-only audits. Source
`da65a5c43b266f4b171bcd2605efa0cff32718b27839f70d468d8508c1a4e126`;
olean
`af6857fe7f683aa93c00281349fa1ff6cb4edc0bd148a0a7a7c4d94da2419f07`.
The checked public endpoints are `fold_zero_iff` and `query_zero_iff`.
Both preserve the image, representation, true-final and local legality
premises; the ordered-query endpoint leaves the oracle reference arbitrary.
All17 audits across the three retained leaves use only `propext`,
`Classical.choice`, and `Quot.sound`. No diagnostic tactic, local operation
override, `sorryAx`, or400 setting remains in these frozen sources.

The focused runner uses MemoryHigh8GiB, MemoryMax10GiB, MemorySwapMax0,
CPU200%, Lean `-j1 -M9500`; native package cache revisions and the borrowed
V7 source pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5` are recorded by
the manifest. Limits are unchanged.
