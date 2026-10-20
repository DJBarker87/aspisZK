# Original polynomial finish numeric bridge (source-only evidence)

This packet composes the corrected original frozen Rust polynomial body, its operational Aeneas loop adapter, the current unrolled finish implementation, and the checked numeric-equations theorem. The new theorem is `AspisR1CurrentWide.OriginalPolynomialFinishBridge.s2_original_polynomial_numeric_equations`. It gives both rounds’ canonical outputs, coefficient traces at indices `[6,5,4,3,2,1,0]`, decoded Horner equations, and the existing finish guards and equalities for the original-body operation record.

The original verifier provenance is the frozen c8 verifier at SHA `8a704eea668d04ca173290ca894c7cb0ab1f29abef4fec9bb49fbb36476779ea`, polynomial span `[12595,12695)` with SHA `ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7`. The matching Aeneas extraction-input span is separately checked; its offset is not misreported as the verifier offset. The body adapter is checked against the emitted Aeneas declaration and operational reverse-range loop.

The bridge removes the unrolled-polynomial operation as an extra finish premise by record/function equality and reuse of the numeric-equations theorem. It does not prove Rust `Range<usize>::rev().fold` correspondence to Aeneas’s operational loop; that remains the explicit library boundary. The packet contains source/evidence only and no compiled object files.

The top-level manifest covers every file in this packet, including the nested frozen packet manifests and all three exact green receipts.
