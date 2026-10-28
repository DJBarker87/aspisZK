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

3. U01 FIo field declarations are selected in replayed closure as
RPz7_FIo_NativeFuns/Types/External. NBG_FIO_SOURCE_SELECTION.json checks all
three complete source texts against the original names used by the coherent
SInt2/LPi objects: every non-import line is identical. Import-name differences
are recorded, not treated as equal object hashes. NBG's value/run proofs are
checked against the actual selected SInt2 objects; no broad old FIo caller
module, XRn_Join kit, stand-in or new interpreter is installed. Explicit field
coordinate ports keep distinct record owners distinct.
