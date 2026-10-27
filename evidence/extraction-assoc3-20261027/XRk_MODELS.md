# XRk external models

All 103 required names now have transparent definitions in the XRk import chain;
the 38 previously missing names are supplied. This is definition coverage, not
source refinement. All twelve whole P6 bridges remain OPEN.

XRk_DecodeModels: decode_k, claims, semantic_boundary and wide_view. Exact owned
references are XRg_decode_reference/claims_reference/boundary_reference and
XRi_reference_wide_view. The row25/offset projections are explicit.
XRk_DotModel: raw u64 wrapping and four folded sums from fast_pairing.rs:88-122;
prepared_claim from XRi_reference_prepared_claim, six scalar branches, 29 dots,
7 powers and first-error short-circuit. No trace effects in release builds.
XRk_CircleModel: closure fallback from XRg_fallback_reference, rational map and
row-specific parameters from circle.rs/transcript.rs. The inverse is an
exponentiation model; correspondence to the source fixed chain is OPEN.
XRk_CheckpointModel: XRi_reference_checkpoint, 3 ordered digests and full byte
serialization. Allocator/Vec/capacity/ownership association OPEN.

XRk_PublicModel reuses the coherent public-preparation implementation with
explicit nested record conversions. XRk_TerminalModel reuses FIq_Native14's
complete terminal with explicit field/array/public/challenge/error conversions.
The adopted FIq carrier wrapper pulls a missing PAln_RowBounds dependency; the
new model instead imports the narrower complete native terminal and writes its
own conversions. No source or cache is overwritten. L032 and L033 audit the
native and converted terminal: standard axioms only.

The historical AspisR1SelectedMaskProbe.Funs object does not expose the raw
terminal declarations: L030 records unknown names. It was not substituted for
the complete terminal. L031 is a missing-dependency failure of the broader
FIq_Terminal import; its failed context is not accepted.

Every external's exact type is checked through final Funs elaboration rather
than treating name coverage as type/soundness evidence. No top imports XRk_.
