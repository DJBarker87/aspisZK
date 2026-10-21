# WideExact byte-decoder source binding

This source-only packet checks the exact binding used by the concrete resume
reader adapter. The current `crates/aspis-core/src/field/wide_exact.rs` file is
byte-identical to the retained current-source snapshot. Its `from_le_bytes`
and `from_limbs` method fragments match the retained record-parser extraction
fragments, and the corresponding generated Lean method bodies match across the
record parser, view parser, and current Echeck extraction after removing the
namespace/declaration headers. Run `python3 check_source_binding.py` to verify
these claims.

The semantic canonicality result is reused from
`stage2-resume-prefix-canonical-20261020`: its
`Stage2ResumeConcreteDecoderCanonicality.actualWideDecoder_success_canonical`
maps the retained `AspisR1RecordParser` result coordinatewise into the reader
carrier and applies `ExtractedRecordByteCanonicality.slice_success`. That
theorem proves the input has exactly 32 bytes, all eight decoded limbs are
below P, and the output is their unchanged packed value. The lower-level
`ExtractedRecordLimbCanonicality.from_limbs_make_success_iff` checks the eight
ordered source guards and packing.

The packet proves source and generated-body identity only. It does not prove
Aeneas translation soundness, general Rust/Lean semantic preservation, or the
full `resumeWithOps`/production caller binding. Those remain in their existing
producer and caller packets.

No Lean source changed and no Lean compile was run for this metadata/source
binding check. The canonicality theorem and object are inherited from the
producer packet named below; their original receipts remain authoritative.
