# NFT Lean-discharged opaque operations

Every row is a local mutable record, never a writable static. Replies are unconstrained within the stated broad bounds; natural product values are substituted only in Lean. This is the adopted opaque-call-log form, not multiplication proved in Kani. No unpaired row is admitted.

| Native site / oracle | Caller-established domain | Paired emitted-definition / value theorem |
|---|---|---|
| CM31::square primitive product (`NFT_square::product`) | canonical a,b<P; exact u64 factors a+b and a+P-b; product fits u64 | NFT_Square.wide_product, existing squareOperand_success |
| CM31::square M31 product (`NFT_square::multiply`) | exact same canonical a,b<P; reply constrained only to <P | NFT_Square.generated_scalar_product through generated_m31_mul_eq_probe; scalar_product and source |
| Karatsuba `mul_by_r(m1)` (`NFT_karatsuba::mul_r`) | exact reached reconstructed m1, both limbs<P, checked by native assertion K036 | NFT_Karatsuba.mul_r_value and mul_r_eq_hiding; full G substitution NFT_Karatsuba.source; total |
| cm31_mul_r double a / double b (`NFT_cmr::op`, kinds 0,2) | canonical exact receiver; zero dummy second argument; replies<P | NFT_Cmr.double_value; exact site ordering NFT_Cmr.source |
| cm31_mul_r subtract (`op`, kind1) | exact first reply and original b, both<P | NFT_Cmr.sub_value |
| cm31_mul_r add (`op`, kind3) | original a and exact double-b reply, both<P | NFT_Cmr.add_value; whole natural value NFQ_Linear.source |
| accumulation channel primitive product (`NFT_channels::product`) | each exact cached operand<P; reply<2^62; pre-cell<3*2^62 | NFT_ChannelModel.product_bound and addition_bound prove broad admissibility. Native/emitted full helper association is OPEN; no composed credit yet |
| m31-dot term primitive products (`NFT_dot::product`, four ordered sites) | four canonical receiver limbs and scalar<P; replies<2^62; raw prestate<3*2^62 | same product_bound / addition_bound. Full native/model loop association is OPEN; no composed credit yet |

The closed-field rows retain P6/D188 NativeContractSemanticTransport option A as reclassification, never premise removal. No Kani expression assumes an exact variable multiplication. Source-site erasure receipts identify the exact replaced sites. Every credited callee domain is proved at its actual caller, rather than imposed on an unrelated external reference.
