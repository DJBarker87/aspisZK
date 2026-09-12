# Successful source/gamma coordinates

## Result

`FSLiveSourceThenGammaV7Decode.successful_trace_components` eliminates the
private return/abort wrappers of a successful chronological source-to-gamma
trace.  It constructs the actual first circle trace and the actual distinct
second trace, including the intervening source callback and answer-row
absorption.

`FSLiveSourceThenGammaCoordinates.successful_source_coordinates_or_data` uses
those constructed traces to derive canonical QM31 coordinates for both OOD
points.  It then executes the same-body `fromSampled` constructor and exposes
the total result as either explicit rejection or checked OOD data.

This is a deterministic source/causality bridge.  It proves neither challenge
freshness nor the random-oracle distribution.  It also does not prove that a
successful complete verifier reaches the `some data` branch; that implication
must come from the complete source execution and its nonzero chord/inverse
checks.

## Focused check

- Target: `FSLiveSourceThenGammaCoordinates.lean`
- Base revision: `133ec6773b14630d30daca4b0360ff305d307feb`
- Lean: pinned 4.32 environment on the NUC
- Cache: private union of pinned base and V8 overlay artifacts; dependency
  sources were not rebuilt by this focused check
- Exit: 0
- Wall: 2.69 seconds
- Peak RSS: 6,616,900 KiB
- Swap: 0
- Source SHA-256:
  `c5a90223faddd69f2ae1a5a315aec0a131abf9a69fff7944d96c2d730f5945d4`
- OLean SHA-256:
  `355018242cc319c1e6a67e01d8a6cd96224ad60ee946f817193e7ba9d2adf25c`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

No wire format, verifier acceptance, probability ledger or CU claim changes.
