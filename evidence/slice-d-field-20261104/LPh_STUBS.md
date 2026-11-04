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
| accumulation channel primitive product (`NFT_channels::product`) | each exact cached operand<P; reply<2^62; pre-cell<3*2^62 | NFT_Dot.scalar_product proves exact emitted U64 product; NFT_ChannelModel.product_bound/addition_bound prove broad oracle admissibility. Whole helper association is OPEN; no composed helper credit |
| m31-dot term primitive products (`NFT_dot::product`, four ordered sites) | four canonical receiver limbs and scalar<P; replies<2^62; raw prestate<3*2^62 | NFT_Dot.scalar_product (exact same U32 inputs widened to U64), product_bound/addition_bound. Actual term/loop laws AspisR1.FJh_M31DotInput.source_success and AspisR1.FJh_M31DotChunkModel.loop_success_fuel; full seven-term source NFT_DotSource.source; fixed chronology NFT_Dot.control and native K070/073, same-window K076/077. Only the caller-established seven-term D domain is CLOSED |

| prepared3 selected channel product (`NFT_prepared::product`) | same left cache/right cached words<P; actual pre-cell≤2*(P-1)^2, inside native pre-cell<3*2^62; arbitrary reply<2^62 | NFT_Dot.scalar_product; exact emitted runStep_success, loop_success_fuel; NFT_PreparedFrame.frame/control and full NFT_PreparedSum3.source. PreparedFor/constructor establishes every cache bound |
| WideExact::square four-site QM product/square/mul_u log | exact same canonical QM arguments and local canonical replies | **OPEN: not admitted.** K098/099 and argument-corruption K100 provide caller support; full emitted callee value laws and whole coherent square equation remain missing |

NFT_ChannelFour.generated_step and NFT_FieldFrontier.four_fit prove the fourth-product arithmetic bound required by the still-OPEN small4 path; they are Lean-only progress, not extra native closure.

The closed-field rows retain P6/D188 NativeContractSemanticTransport option A as reclassification, never premise removal. No Kani expression assumes an exact variable multiplication. Source-site erasure receipts identify the exact replaced sites. Every credited callee domain is proved at its actual caller, rather than imposed on an unrelated external reference.
