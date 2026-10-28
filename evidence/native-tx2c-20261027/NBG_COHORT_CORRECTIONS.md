# Coherent cohort corrections

1. Digest/error use coherent SInt2 AdapterRwModel slots op43/op44, as the
binding lane ruling requires. NBC's source-selection finding is retained;
op48/op49 in that object are account decoders, never digest/error.

2. NBI2's `WideExact::from_m31` row says no separate counterpart. The coherent
closure contains `S1M31EmbeddingSourceV1`, namespace AspisS1M31Embedding,
`aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31`.
The emitted name includes the CodeField trait instance; it was missed by the
inventory's inherent-method scan. Its exact body is the selected QM31 CodeField
embedding followed by WideExact::from_qm31, matching frozen scalar.rs:89–91.
`S1M31EmbeddingTotalV1` already proves TOTAL raw-input embedding, including both
normalizations; NBG imports that proof unchanged. New NBG_Embedding names the
actual trait member directly and the complete raw-QM31 embedding result.
Selected source/object pins are NBG_SELECTED_OBJECTS.json and the inherited
coherent manifest; source is read from committed evidence/port17release-20261024/
dependency-source, never session A's live worktree. NBI2 is not modified.

No theorem/carrier/dictionary or imported proof is silently identified merely
by matching names. New bridges specify their selected counterpart explicitly.
