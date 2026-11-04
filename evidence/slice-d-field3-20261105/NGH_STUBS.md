# Opaque products and exact domains

| Native site | Named Lean totality/value law | Caller establishes |
|---|---|---|
| NGH_qsquare::op kind0: CM31::square(c0) | NGH_QSquareOps.square; natural coordinates NGH_CMWords.square | same canonical receiver x.c0, from hx.1 |
| NGH_qsquare::op kind1: CM31::square(c1) | NGH_QSquareOps.square; natural coordinates NGH_CMWords.square | same canonical receiver x.c1, from hx.2 |
| NGH_qsquare::op kind2: CM31::mul(c0,c1) | NGH_QSquareOps.product; natural coordinates NGH_CMWords.product | both same canonical receivers hx.1/hx.2 |
| NGH_contracts::opaque (one U64 channel product) | NFT_Dot.scalar_product, NFT_ChannelFour.generated_step, NGA_Step.source | a,b<P; selected sum≤3*(P-1)^2; reply≤(P-1)^2; four-product bound <2^64 |
| Inherited WideExact square four local-record sites | NGA_NativeOps.product/square/mul_u; NGA_WideSquare.value/source | canonical c0/c1, and canonical bb derived from the SAME square result |

NGH_QSquareOps.associate and source substitute the actual operations on the SAME input and replies into the exact emitted square body. Real mul_by_r, addition and double remain ordered. No loop or multiplication is evaluated in the admitted Kani square log. K011 passes; K012 result corruption and K013 argument corruption fail; K014/015 are the matching QM copy pair with exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

K010 used kani::stub CM31::square -> NGH_qsquare::square and CM31::mul -> NGH_qsquare::product with kani::any constrained by the natural-coordinate formulas. Its matching law is NGH_CMWords.square/product, but K010 TIMED OUT and has zero credit. It was replaced by the log shape, never rerun unchanged. No field multiplication is proved by Kani.

The one-cell source contract K017/018 has precise modifies(log), an arbitrary pre-state and complete returned 3x3 array equality against cell_ref. It is support for rule-B induction, not a helper-level proof_for_contract. It cannot close TX1:036 by itself.

No writable static, Option<fn>, or stub_verified field callee is used. The pure 3x3 interface controls K002..009 establish ruling-(t) fidelity; they do not prove an unverified callee.

Resume cell attempt: NGH_cells::native_product -> product_stub is paired with NFT_Dot.scalar_product (raw U64 cast multiplication on canonical M31 words), NFT_ChannelFour.generated_step (four-product checked-add bound), and NGA_Step.source (same factors/selected old sum and complement frame). Domain a,b<P, selected old sum≤3*(P-1)^2; the exact cache prelude and NGA_CacheDomain.source establish factor bounds. The native/reference stub reply is kani::any constrained to the natural product. K049 timed out, so this pairing supplies no native cell credit. The actual frozen cell contains one product.

The outer-step cut has no product stub: it exposes the actual accumulation child as an arbitrary complete reply in a local record. Its native chronology/frame does not establish that child's semantics, and it is not stub_verified as a CLOSED child. The existing NGH_AccumulateRef.model_eq and NGH_OuterRef laws associate that SAME child model only.
