# Actual scalar M31 multiplication source map

This focused proof maps the attempt16 generated actual `field.M31.mul` body to `.ok (R22CurrentReducerMul.wrappingMul x y)` for every `Std.U32` pair. It composes the source body with the actual source-reducer-to-R22 result theorem and the specialized U64 multiplication compatibility theorem. The theorem has no canonicality premise and does not itself claim higher-level `WideExact.mul_m31` refinement.

The source cut, reducer foundation, and U64 compatibility are pinned by the sibling packets listed in `dependency-pins.json`. `evidence/` holds the exact focused Lean command, preflight, receipt, axioms output, and resource report. Compiled objects and full transitive closure snapshots are excluded.
