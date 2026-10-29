# ActualInput binding audit, D469

The accepted Link definition is unchanged. `PV_OWNO_ActualInput` is a source-stage
composition, not an unconditional theorem about the deployed execution.
Its `built` premise is successful evaluation of the explicit builder value
projection. Its `writes` argument is an operational point-store sequence;
installation requires the actual callback/final point to equal that sequence.
Neither premise may be replaced by a bare canonicality hypothesis.

## Exact native stages and proposed model association

- `state_only_candidate_prefix.rs:785–804`: the early disjunction rejects any
  C1 length different from1024, any base limb >=P, and any d/g write/read
  roundtrip rejected by QM31::from_le_bytes. `Builder.acceptedBase` and
  `acceptedExtensions` model these successful checks. `InputBytes` proves the
  numeric LE roundtrip. Native `any`/`chain` and exact byte carriers still need
  complete Result/array-to-List association before installed credit.
- `:805–820`: construction of base/first, C1 commitment, transcript creation,
  lambda and chi. `Builder.setup` preserves the first returned error and permits
  arbitrary successful lambda/chi. It is an opaque continuation, not a proof
  that these source steps have been bound. Input canonicality need not constrain
  the challenge values at this stage.
- `:821–825`: helper, length conversion, sum check. `HelperSelect` retains
  upstream registry errors and maps ActivePole to imbalance; `Builder` retains
  length and balance failures. The final Error::Public mapping is the source
  closure at `:980–991`. The exact outer error map and helper value projection
  must be associated with that closure, not inferred from a function name.
- `pair_forest_semantic_oracle.rs:171–179`: registry then selected helper,
  mapping LogUpError to CopyImbalance. The generic registry result admits all
  rows, hence no registry canonicality premise is needed. This eliminates
  any need to prove a particular trace's values or inverses canonical.
- `logup.rs:192–225`: capacity, forward enumerated row traversal, ZERO,
  producer two-slot array zip, weight-zero test, sub/try_inv/ActivePole,
  mul_m31/add, consumer array zip and sub, push, return. `HelperArrays` uses
  the actual Aeneas fixed-array length carrier; `HelperPush` retains forward
  initialization timing. World/ownership and unwinding remain for OwnedPublicPlan.
  `HelperResult`'s changed bind conversion and substitution repair is accepted
  at66850, with all six standard-axiom reports.
- `state_only_candidate_prefix.rs:826–844`: C2 commitment and scalar rows2–13,
  followed by the ordered26 lifts/h1/g/d construction. `Builder.finish` retains
  these failures as a continuation; `Inputs.columns_canon` handles the exact
  successful concatenation. Complete native continuation association remains.
- `r0_transcript.rs:126–155`: all eight divisions, every quotient store and
  returned remainder, then decode first four. `SampleEight` permits arbitrary
  dividend/quotient rank influences for canonicality. The modulo result is
  bounded for every U64, so reduce_rank, quotient orientation and shift/OR
  arithmetic identities are not canonicality premises. The fixed-array loop
  and actual U64 remainder/cast carrier still need source-execution binding.
- `state_only_hiding.rs:1593–1627`: point initialized to ten ZERO values;
  sample<28, all Boolean suffix stores, and sampled challenge stores. These
  are the three `PointStores.Write` constructors. Bound indices are Fin10.
  `run_canonical`/`run_length` prove the invariant for every sequence, including
  rejected prefixes. A native source trace must produce that sequence, with
  every reached index proved in bounds. The terminal callback observes the
  final ten challenge stores; it is not another round<10 sample query.

## Remaining links, in mandated order

ActualInput remains OPEN until those concrete value/carrier/continuation and
point-trace associations are established. Local composition is not installation.
OwnedPublicPlan is OPEN: exact op222 Slice/array carriers, initialized sparse
bytes, ownership moves, IntoIter/drop and global first-stop resource trace.
Transcript879/890 are deferred until those prior links hold. Existing runjoin
laws are read-only. Merged b3p6 op227 modules do not assert V239's links; their
own resume12 report retains the actual caller/stdlib/callback obligations.

T and all five Link definitions are unchanged. V370/D381/D386 and rdea-1
remain named boundaries. No new cryptographic/runtime assumption is introduced.
