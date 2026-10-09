# Same-body authenticated slots: DRAFT, NOT COMPILED

Historical draft note, retained below. Subsequent v3 passed the historical
toolchain leaf check; see [current status and evidence](authentication-connection-20260912.md).
The patched full dependency rebuild remains open.

Source base inspected: `93cab4705bc39beb8fb5649c153e2529633e270c`.
`lean/SameBodyAuthenticatedSlots.lean` awaits exact historical import-source
resolution and a fresh first-party build. No checked endpoint is claimed yet.
The earlier `PackedQueryResidual` suggestion is withdrawn as a checked
predecessor: artifact review reports failed attempts rather than a green
artifact. This draft does not import it.

## Target and producer

The target takes a functional `SuccessfulMerkleRun view query body`, successful
canonical parsing of its own22 records, explicit phase prefixes and answer/log
laws. It returns the existing concrete authentication-failure union OR
constructs decoded records and proves all four slot equalities between the
body-derived records and the gamma batch of both prefix-derived words.

`collectFin` is a finite Option traversal; `parseRecords` runs the existing
canonical parser at each `wire.record` in ordinal order. The outer theorem
does not take independent decoded records, `FixedInput`, a supplied total word,
or an assumed equality identifying such a word with an early commitment.
The `canonical` input is the actual functional parser's `isSome` result;
literal Rust parser success still needs to imply it. Executability of this
composition has not yet been compiled/tested; historical canonical field
models may require a separate efficient executable realization.

## Dependency composition

1. `SelectedWireMerkleRun.successful_constructs_accepted` produces Accepted
   over this Wire's roots, raw record projections and frontier halves.
2. `accepted_all_projections_or_shared_failure` produces per-ordinal C1/C2
   projections or shared digest collision/C1 late target/C2 late target.
3. `batch_slots_of_paired_projection` and `raw_slots_of_paired_projection`
   yield the exact gamma-combined slot equalities for the decoded/raw records.
4. `successful_record_is_body_record` makes the records explicitly literal
   offsets in the submitted body, not independently supplied records.

## Premises that are NOT discharged

- Functional Merkle verification and canonical field/body parsing must be
  constructed from actual selected Rust success (including variant ordering).
- Prefixes must come from chronological C1/C2 cuts, not arbitrary log subsets.
- Answer equalities and prefix/call inclusion are explicit premises here;
  current Std FS history theorems are not yet coupled to these historical
  types and effectful source hashing.
- A gamma argument is provided; this slot theorem holds pointwise for any
  gamma and does not assert a fresh or uniform distribution.
- The supplied query ordinal vector must be produced by the real sampler;
  no real-transcript sampler theorem is claimed.
- Authentication alternatives remain UNCHARGED probability events.
- This is raw component batch equality, not yet a quotient/fold/positive-query
  update, full relation acceptance, extraction or global soundness theorem.

Next dependent arithmetic should use the verified variant
`SelectedPackedQueryBridgeV3.matching_fold` with the authenticated local slot
equalities. Its `observedWord` must not be retroactively frozen as an early
oracle. Do not silently substitute differently named or stale artifact variants.
