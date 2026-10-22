# S9 scalar-factor source-vector meaning (source-only)

This packet freezes `AspisR1S9BodyPrefixScalarVectorV1.scalar_factor_vector_meaning`. It derives the S2 scalar polynomial from the same active-body scalar result and the exact four PERM-indexed reads in the returned `BodyPrefixWitness`. The witness's source array reads are connected to `cells ap0` through the accepted index-to-cell theorem; no independent vector or scalar premise is assumed.

The result is within the selected helper model. It does not prove frozen Rust `core::array::from_fn` correspondence or complete S9 closure. The Lean object is intentionally not included.

Run `python3 check_packet.py` to validate source/profile/receipt/import pins and the named axiom report.
