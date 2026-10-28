# NBA return abstractions and Lean pairings

**Composite status OPEN. A passing routing gate is not a proved callee law.**
All NBA return abstractions are supersets of the legal concrete returns, or
terminal cuts. No field multiplication is evaluated in Kani. There is no new
field-operation stub. Translated multiplication is reused through the CLOSED
LPi/LPq/LPt callee arguments and their existing emitted/probe equalities.

| Replacement/cut | Domain and caller discharge | Named Lean pairing | Actual credit |
|---|---|---|---|
| scalar / NBA_route_gamma / NBA_route_ordinary | typed block; rows27..30; reached payload<=2048. Output canonicality from SAME producing gamma/ordinary call | NBA_SamplerValues.gamma/ordinary/scalar; NBA_Scalars.gamma/ordinary; CLOSED LPk low; NBA_AddPair.source and decode8_candidate_eq_retained | K004 prefix, K030 actual scalar routing; K031 low/add/decode call routing. Whole native sampler-to-installed child join remains OPEN |
| NBA_route_block | SAME transcript state, row27..32, payload<=2048; native digest always returns32 bytes | NBA_Transcript.absorb/block on three SAME framed digest observations | K007 native block; K030 call/routing/state, no assumed block Result equality |
| queries / NBA_query_decode | typed8 blocks/advances, every32-byte input; default valid scanner and per-word bounds preserved by NBA_QueryStep.valid | NBA_QueryWords.source, QueryNative.source/construct, QueryTrace.source/unique, QueryDriver.source, Materialize.source, QueryJoin.source | K013-K016 one-step/core/finish; K023/K024 full eager wrapper Result and state. Complete native decoder/trace-embedding child association OPEN |
| scalar_k / NBA_route_qm | SAME32-byte block; row32 empty payload at two-fold caller; four division callbacks | NBA_Rho.source (all coordinates and SAME4-pass trace), NBA_RhoScalar.source; SamplerTransport.sample_total; PreparedFromQmSourceBridge.fromQmSource_success | K017 caller route, K030 actual scalar_k, K032 division step. Whole child association awaits complete driver/packing join |
| powers29 | N=29; canonical gamma derived from SAME row27 call; caller uses exact returned array | NBA_PowersCallee.source: successful emitted FIo_Native.weights.powers and exact installed array, all canonical. Inherited LPq_Powers.source/LPi translated multiplication | K022 aligned arbitrary-array scratch transfer, K017 call arguments; no multiplied value assumed/proved by Kani |
| claim | canonical semantic coordinates, inactive/kappa/weights; checked compact464 actual expansion928. SAME finish/wide_view/scalar producers, not arbitrary typed View | NBA_ClaimCallee.source, ClaimTotal.construct, ClaimInputs.source, CLOSED LPt_PreparedClaim native_result; LPt_ByteDomain.checked_expanded and LPs_SemanticDomain | K019 SAME actual call arguments; caller's entire native producer/domain join remains OPEN |
| QueryScan membership Bool | len<=22, draws<=64; SAME accepted prefix, arbitrary candidate. Default and every Frame preserve bounds | NBA_QueryStep.fresh/duplicate plus actual stdOps.contains; NBA_QueryTrace.source induction | K013 universal Bool overapproximation. Instantiate with actual pure contains under retained TrustedStd, not a new membership assumption |
| NBA_low_route | all32-byte blocks. Guarantees only canonical8 digits and q<=256, admits every such return | CLOSED LPk_Result.native_result; LPk_Cohort.all_blocks. Exact digits/q supplied by that bridge, not assumed by routing gate | K031 call/input identity and downstream domain bounds |
| NBA_add_route | canonical8 digits; first addend=q+1<=257 from low result; second addend=1. First output arbitrary canonical8 digits/Bool; second call is terminal | NBA_AddCarry.step/source/construct, NBA_AddPair.source: exact emitted add-small value/carry on SAME local trace | K027 ONE digit/frame, K031 call routing and wrapped second-add cut. No credit for execution beyond terminal cut by K031 itself |
| NBA_decode_route | canonical8 digits established by low or add output | AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.decode8_candidate_eq_retained; NBA_SamplerValues ordinary/gamma totality | K028 actual native decode8 preserves every coordinate; K031 terminal decoder argument check |
| NBA_pass_route | every8-u32 rank; incoming remainder0, descending j=8..1 with r<P preserved | ExtractedQM31SamplerPass.body_success, ExtractedQM31SamplerPassLoop.loop_correct; LPk_Step.unique, LPk_Induction.pass_join/digits_join; NBA_Rho.four_digits/source | K032 ONE native descending iteration, K033 planned ONE outer callback. Complete SAME4-pass native association remains explicit OPEN work until joined |

NBA_Carriers.roundtrip/canonical and NBA_ClaimCallee.port/array_port preserve
all words. NBA_Inactive.limbs/bytes derive canonicality from the SAME emitted
successful decode; NBA_WideView.inactive uses the reached cohort parser.
LPo's CLOSED wide_view native bridge supplies its corresponding native leaf.
NBA_PrepareSuffix.source still receives these producer facts and child calls;
it does not discharge their native construction by wrapping them in a structure.

Inherited multiplication pairings remain the exact LPq_STUBS.md and
LPh_STUBS.md from their CLOSED packets. LPm_emul pairs LPi_TowerValues.wide_mul
on canonical operands; private Dot pairs LPm_PublicState.private_source and
LPi_RawValues.source on arbitrary u64 pre-state/canonical packed operands.
LPb replay provenance is LPi_REUSE.md's LPe_K001/K004-K007 frozen-stage mapping;
no new LPb rerun is claimed. Every actual NBA Kani run independently validates
its frozen package/edge closure, runs offline, and confirms unchanged lock.
