# V7 Tag-73 inner transcript/relation source translation

This bundle freezes a literal Charon/Aeneas translation of the production-core
function
`aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner`
from `main` commit `c9bbf8d3`.

The selected root is the live fail-closed inner verifier path: transcript
setup, canonical fixed-field parsing, the semantic relation, query scheduling,
and terminal preparation.  The three independently translated components are
left as explicit extraction boundaries in this combined translation:

- `verify_compact_semantic_sumcheck`;
- `decode_and_absorb_point_claims`;
- `decode_and_absorb_final256`.

They are frozen separately in
`aeneas-verif/v7-tag73-transcript-components-20260913/`.  Other listed
opaque functions are likewise explicit source-extraction boundaries, not
trusted verifier outputs.

## Reproduction

The source was created with `git archive c9bbf8d3`, Charon 0.1.223 using the
`aeneas` preset/built MIR/default sysroot, and the pinned
`aeneas-d860-v6-linux` Lean backend:

```sh
charon cargo --preset aeneas --mir built --sysroot default \
  --start-from crate::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner \
  --opaque aspis_core::sumcheck::_::weight_at \
  --opaque aspis_core::sumcheck::_::dot \
  --opaque aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major \
  --opaque aspis_core::field::qm31_dot3 \
  --opaque aspis_core::v6_transcript::verify_compact_semantic_sumcheck \
  --opaque aspis_core::v6_transcript::decode_and_absorb_point_claims \
  --opaque aspis_core::v6_transcript::decode_and_absorb_final256 \
  --dest-file V6InnerR6Prefix.llbc -- \
  --locked --package aspis-core --lib --features aeneas-observer

aeneas -backend lean -namespace V6InnerR6Prefix -dest generated \
  -split-files -emit-json -impl-namespace -loops-no-rec V6InnerR6Prefix.llbc
```

The generated output completed successfully in 13:07.64, with maximum RSS
3,762,072 KiB and zero swap. `LLBC-SHA256SUM` records the raw Charon output;
`SHA256SUMS` covers every committed generated file.

## Scope

This is a source-translation milestone, not the final accepted-source
theorem. `*_Template.lean` files are archival output and must not be imported.
The remaining work is to provide executable external models and prove the
source-to-K1.3 pre-query-view correspondence, then kernel-check the composed
bridge. The only intended cryptographic primitive boundaries remain the
project's declared Poseidon, SHA-256, and circle-code interfaces.
