# Retained stub pairing

| Stub / context operation | Named Lean theorem | Domain |
|---|---|---|
| NEK_Context::NBG_product, local-record replacement of historical NBG_product/M31::mul | AspisR1.LPf_BaseMultiply.source; retained NBG_STUBS.md, NBG_L010 and NBG_SquareLoop.square_n_result | ALL raw u32 operands, established by Rust input type. Arbitrary canonical u32 result constrained to natural (x*y)%2147483647. No multiplication proved in Kani. |
| Exact KMX copy replacements | KMX_CopyMeaning value/frame laws, inherited frozen patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | Existing copy validity/domain obligations and matching failing control retained per configuration. |

No new field stub theorem is assumed. Domain/semantic transport trust is retained, never removed.
