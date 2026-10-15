# Exact generated field declarations reused in wide-parser attempt d

Attempt d's current `field.rs` input has SHA-256 `28df5a1a…f1baea`, identical to the input used by the successful 2026-10-14 field parser extraction. After normalizing only the generated namespace name (`AspisR1CandidateParser` to `AspisR1WideParser`), the following generated declaration blocks compare byte-for-byte:

- Types: `field.M31`, `field.CM31`, and `field.QM31`.
- Functions: `field.M31.from_le_bytes`, `field.CM31.from_le_bytes`, and `field.QM31.from_le_bytes`.
- Core Option helper bodies: `Try::branch` and `FromResidual<Option<Infallible>>::from_residual`.

The normalized block SHA-256 values are recorded in `manifest.json`. The prior generated source is in `../field-parser-candidate-20261014/field-parser-candidate-attempt-a.tar.gz`; its `Funs.lean` SHA-256 is `88817c53…f15c776`, and `Types.lean` SHA-256 is `b1122429…31e80067`.

Attempt d additionally generated `field.wide_exact.WideExact` with two QM31 fields, its `BYTE_LEN` constant, `field.wide_exact.WideExact.from_le_bytes`, and the probe wrapper. All generated functions in d are marked non-opaque in `translation.json`. The standalone Lean output is retained as extraction output and was not compiled here.
