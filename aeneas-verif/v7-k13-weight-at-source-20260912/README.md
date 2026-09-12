# V7 Tag-73 `WeightAccumulator::weight_at` source extraction

This focused Aeneas artifact removes the temporary opaque `weight_at`
interface from the K1.3 pre-query observer work.  It is deliberately a small
source component: it does **not** claim the adversary-first Fiat--Shamir
causality theorem, which belongs to the shared lazy-oracle scheduler.

Pinned production revision: `ccc19c1cecfaf2526edd3d3a5277c7b54b0a77bf`.

Extraction target:

```text
aspis_core::sumcheck::WeightAccumulator::weight_at
```

The generated Lean source has two external standard-library operations only:
`Option::as_ref` and shared `Vec::into_iter`.  Their executable models are in
`generated/V7WeightAtStandalone/FunsExternal.lean`; neither is a
project-specific axiom.  The extraction completed on the pinned NUC toolchain;
the generated-Lean replay must be run with the matching Aeneas Lean backend
rather than an incompatible historical cache.

`weight_at` itself has no source change relative to `155b92ce`; the later
changes to `sumcheck.rs` are confined to the `WeightAccumulator::dot`
terminal fast path.

The next source bridge must use this component only to establish the concrete
verifier pre-query calculation.  It cannot be used to assert that an
arbitrary adversary fixed that calculation before a first random-oracle
exposure.
