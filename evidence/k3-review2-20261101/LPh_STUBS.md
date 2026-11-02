# Retained stub pairing

| Stub / context operation | Named Lean theorem | Domain |
|---|---|---|
| NEK_Context::NBG_product, local-record replacement of historical NBG_product/M31::mul | AspisR1.LPf_BaseMultiply.source; retained NBG_STUBS.md, NBG_L010 and NBG_SquareLoop.square_n_result | ALL raw u32 operands, established by Rust input type. Arbitrary canonical u32 result constrained to natural (x*y)%2147483647. No multiplication proved in Kani. |
| Exact KMX copy replacements | KMX_CopyMeaning value/frame laws, inherited frozen patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | Existing copy validity/domain obligations and matching failing control retained per configuration. |

No new field stub theorem is assumed. Domain/semantic transport trust is retained, never removed.

| Transitive NEA local-context operation | Retained named emitted/model theorem | Caller domain |
|---|---|---|
| NEA_point::cm_mul(ctx, x, y), opaque canonical product/call log | NEA_FieldProduct.emitted_cm; NEA_FieldProduct.geometric_cm; NEA_TableCanonical.readA/readB | Both selected table operands canonical, asserted natively. Every canonical reply is overapproximated; Lean selects the exact emitted product. |
| NEA_line::point_cut(ctx, u) | NEA_PointComplete.cohort | Same u.get()<262144; exact argument logged; canonical returned coordinates. |
| NEA_line::m_mul(ctx, x, y), opaque scalar product/call log | AspisR1.ExtractedCurrentReducer.current_mul_mod (NEA_L059) | Both canonical operands; native post checks both equal the returned point.x. |
| NEA_line::m_double | NEA_LinePrimitive.double_value | Canonical input; exact natural double residue on the arbitrary reply. |
| NEA_line::m_sub_one | NEA_LinePrimitive.sub_one_value; NEA_LineTail.sub_one | Canonical input, rhs=1, both asserted in the original stub. |

These are exactly the imported NEA register's laws (NEB_IMPORTED_POINT/LPh_STUBS.md), with explicit local log parameters. No field multiplication executes in Kani. Fresh count-zero ghost inputs are explicit for the non-opaque point/line contracts and are established by harness initialization and the unselected fresh-context adapters. Opaque-line entry reset is retained. All source/context transport and cohort associations remain explicit P6/D188 qualifications.
