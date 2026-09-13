# V7 K1.3 pre-query snapshot source translation

Literal Charon/Aeneas translation of
`snapshot_query_batch_prechallenge` from source commit `c9bbf8d3`.
The generated function computes the exact source-side terminal discrepancy
`running_claim - weights.dot(final256[..4])` and copies the transcript state,
gamma, alpha, query schedule, selector, counter, and frontier metadata at the
pre-query-batch boundary.

`WeightAccumulator::dot` and `weight_at` are explicit separately translated
accumulator boundaries; no snapshot field is trusted. The output is intended
for composition with the current inner transcript source translation at
`aeneas-verif/v7-tag73-inner-transcript-source-20260913/`.

Charon 0.1.223 and the pinned Aeneas Lean backend completed this translation
with `-split-files -emit-json -impl-namespace -loops-no-rec` in under two
seconds, maximum RSS 435,544 KiB, and zero swap. `LLBC-SHA256SUM` and
`SHA256SUMS` make the extraction and generated outputs replayable.

This extraction does not itself prove the full K1.3 prefix-factorization
theorem; it supplies its literal local source calculation. Template files are
archival and must not be imported.
