# Live relation construction from sampled OOD data

`SameBodyLiveRelationFromSampled.buildFromSampled` closes one caller-input seam
in the functional source chain.  Given the actual OOD result, gamma and body,
it first runs the executable `fromSampled` parser/interpolant constructor.  A
failure is an explicit `sampledData` rejection.  Only returned data are passed
to `SameBodyLiveRelationObservation.build`, whose failures remain separately
classified.

Successful construction proves:

- `fromSampled ready.out ready.gamma ready.body = some ready.data`; and
- `ready.data.Checked`.

This constructs, rather than assumes, OOD-data provenance at this boundary.
The whole chronological selected verifier is not yet defined in terms of this
wrapper, and the result supplies no freshness or probability law.

Focused NUC check on base `abba7ca5` used the pinned Lean 4.32 environment and
the private base/overlay union cache.  Dependency sources were not rebuilt.
Exit was 0, wall time 8.42 seconds, peak RSS 6,747,956 KiB and swap 0.  The
source SHA-256 is
`2344bde217cbcae0f4c00b153b2be2a6cebeac701af23dde85b48a6726991cbc`;
the OLean SHA-256 is
`5d8a50c5b0feb2daaf9b11529dc0dfab32b6b1dff0e27c10d5e23faea1c75090`.
Both promoted theorems print only `propext`, `Classical.choice` and
`Quot.sound`.

No protocol, body, verifier acceptance, probability or CU claim changed.
