# Recovered-high fork extraction — 2026-09-12

## Result

`RecoveredHighForkExtraction.recovered_components_mem_family` proves a new
deterministic extraction bridge for the middle-radius recovered branch.  Two
further checked consumers now prove that the constructed tuple has the fixed
family's own-support and early-C1 projection facts, and that all 87 component
point claims equal the corresponding covector evaluations.

For 29 distinct gamma nodes and four distinct alpha nodes per gamma, assume
the same fixed execution and the same family of cardinality at most one supply
an actual `RecoveredMiddleFork` at each of the 116 continuations.  The
extractor then:

1. reads the four disclosed final256 vectors for each gamma;
2. reconstructs that gamma's canonical 1,024-element quotient using the
   existing four-alpha interpolation;
3. reconstructs its original batch word; and
4. interpolates those 29 batch words in gamma to obtain 29 component messages.

The theorem concludes that this computed tuple is a member of the fixed
family.  The member is not passed to `recoveredComponents`, and family
membership is not an assumption about the computed result.

`recovered_components_family_facts` derives, for that same computed tuple,
the family membership, at least 38,228 matching original symbols, and
membership of its C1 projection in the pre-lambda/chi early family.
`recovered_components_claims_exact` uses the actual row witnesses carried by
the same 116 continuations to prove all three rows and 29 lanes exactly.  It
does not assume a component-claim correctness predicate.

The supporting `tuple_eq_of_batches` theorem proves injectivity of the
degree-28 scalar-power curve at 29 distinct nodes.  `fork_middle` derives the
lower middle support bound from the actual `HighSupport` definition and the
full/bad fibre partition.  The upper middle bound remains explicit because
`RecoveredHigh` also covers quotients above the middle-radius cutoff.

## Access and cost

The candidate-only extraction interface consumes:

- 116 successful continuations;
- 256 QM31 final coefficients per continuation;
- 29,696 QM31 values, or 475,136 source bytes at 16 bytes per value;
- deterministic four-alpha and 29-gamma interpolation work.

These are extractor resources, not extra proof-body bytes or verifier queries.
The V8 proof body remains 40,282 bytes.

The result does **not** prove that a ROM fork collector obtains the required
continuations within bounded work.  Every failed continuation, replay,
authentication failure, cache hit, retry and oracle query must remain in the
same probability/resource experiment.  The theorem also does not cover the
near/high branch above the 252,847-fibre middle upper bound.

## Why the fixed-window decoder is insufficient

The q22 proof supplies only 88 opened evaluations per C1 column, leaving
linear nullity at least 936 for a 1,024-coefficient message.  The implemented
recorded-prefix resolver reconstructs fixed fibres 0 through 255 using 521
recorded lookups, and the existing `recover_c1` performs exact interpolation
on that window.  `RecoveredHigh` guarantees only 38,228 component agreements
at unspecified positions.  It does not guarantee correctness on the fixed
window.

The selected Gao theorem is a genuine near-radius decoder, but its checked
interface requires at least 1,025 samples and at most half the residual
distance in errors; the current selected wrapper uses 513 fibres and at most
128 bad fibres.  It cannot be applied to the minority-support recovered tuple.

Consequently, the 29-by-4 final-only route is the first current construction
that derives the recovered family member without assuming access to it or
adding authenticated openings to the proof.

## Focused evidence

The extended leaf passed on the NUC under the pinned Lean 4.32.0 binary in
`aspis-recovered-forks-v10.scope`, with `MemoryHigh=8G`, `MemoryMax=10G`, swap
disabled and a 600-second runtime cap.  It completed in 4.66 seconds wall time,
used 6,682,372 KiB maximum RSS and zero swap.  `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound` for all six promoted theorems.

This is a focused historical-cache check, not a clean first-party rebuild,
patched-toolchain replay or external validation.  Machine evidence is in
`results/v8-completion-fs-extraction-20260911/recovered-high-forks-v10/report.json`.

## Next theorem

The decisive next endpoint is a bounded collector theorem:

```text
one accepted source-coupled execution in the recovered middle branch
  -> 29 distinct gamma nodes and four useful alpha continuations per node
     with the same fixed commitments/family and authenticated final256 values
  OR an explicitly charged fork/target/authentication/resource failure.
```

Only after that producer exists can the constructed family member be fed into
the same-C1 payment theorem and literal `extract_checked` validator without an
unproved candidate-inclusion premise.
