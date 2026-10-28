# NBL stub / theorem / domain pairings

No new field multiplication stub is introduced. Existing LPi/LPm/LPq/LPt
multiplication pairings are retained through NBA_PowersCallee and the CLOSED
LPt prepared_claim packet, on canonical inputs derived from producers.
No field multiplication is evaluated in Kani. Composite prepare remains OPEN.

| Native replacement | Exact domain and caller proof | Named Lean pairing | Credit |
|---|---|---|---|
| NBL_alloc_fail | actual filled::<u8> call,14759 elements; error arm only | NBC_Filled.result on reservation Err, plus candidate's source Error mapping | K003 local error routing; native allocator remains external/open U00 |
| NBL_alloc_any | arbitrary initialized14759-byte buffer; actual zero initialization is included; size/alignment asserted | Caller geometry K007 and LPt_LPs_ProducerTotal.expansion for y1 | Return overapproximation, not native allocator/ownership law |
| NBL_expand_sem_error / sem_ok | exact compact semantic/logical slices captured at the source call | Assigned semantic-expansion producer remains explicit dependency; errors map via From<CodecError> | K004 local rejection only; no successful producer credit |
| NBL_expand_y1_error | input464/output928; arbitrary local error effects overapproximation | LPt_LPs_ProducerTotal.expansion PROVES no error on this domain | K005/K006 timeout, excluded; K007 proves caller domain; stop probing impossible errors |
| NBL_scalar / NBL_queries_error | same block state, row/payload, and every returned advanced state; query receives alpha1 post-state | NBL_BlockTrace.scalar_result; NBL_OpeningTrace.source; NBL_PrepareResults.query_error | K008 source control/state gate. Child scalar equality is instantiated by NBL_SamplerNative and inherited block/packing gates, not assumed from arbitrary output |
| NBL_low | any32-byte block; no limb restriction | CLOSED LPk_Result.native_result; NBL_SamplerReplay.low | K009 same input/canonical8 digits/q≤256 route; exact low output comes from closed leaf |
| NBL_add first | canonical8 digits, addend=q+1≤257 derived from SAME low trace | NBL_AddNative.source/canonical; NBL_SamplerReplay.increment | K009 input/output carrier route; exact carry/value from native ONE-step NBA_K027 + NBA_AddCarry induction |
| NBL_add second false flag | ONLY reached after SAME first native carry wrapped, with native low/first/second traces | NBL_SamplerDebug.source (c2=0), NBL_SecondCarry.natural, NBL_AddNative.source | Canonicality ALONE is insufficient. The caller's first-trace relation discharges this stronger domain in Lean. K009 source return/debug control, not an independent proof of the second carry |
| NBL_decode | SAME canonical digits produced by low/add | NBL_DecodeNative.source; NBL_SamplerNative.decode_gamma/ordinary/gamma_no_wrap/gamma_wrap; inherited NBA_K028 native pack | K009 exact returned eight-word E; no local decode success premise in strongest Lean theorem |
| NBL_qdigits | all32-byte blocks, four returned canonical digits | NBA_Rho.source/four_digits on SAME four LPk_Induction.Digits passes | K010 actual native qm31_sample packing; source trace association also needs init/loop frames |

All replacements are in an external scratch overlay and retained as patches.
Per-run frozen graph/lock/source receipts apply. Every used emitted theorem is
standard-axiom checked; failed diagnostic sorryAx roots receive no credit.

| NBL_queries_success / NBL_rho / NBL_powers / NBL_claim | K015 source suffix starts at the exact two-fold post-opening position. Arbitrary replies; assertions link query state to rho, gamma to powers, the old/produced SAME scratch pointer and arbitrary slot, and semantic/y1/inactive/kappa to claim | NBL_QueryHashReplay.source; NBL_ScalarHashReplay.rho; NBA_PowersCallee.source; CLOSED LPt via NBL_ClaimDomain.source | Passing control/carrier association, ending at claim cut. Does not prove callees from arbitrary replacements or the full native trace instance. K014 spanning timeout excluded. |
