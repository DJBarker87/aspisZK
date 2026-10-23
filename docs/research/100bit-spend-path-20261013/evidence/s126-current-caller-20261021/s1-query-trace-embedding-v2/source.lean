import S1M31EmbeddingTotalV1
import CurrentOriginalPreparedInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1PublicPreparation.S1QueryTraceEmbedding
abbrev actualEmbed := AspisS1M31Embedding.Total.embed

theorem embedTrace_total {A : Type} (u : U32) (i : Usize) (tail : Result A) :
    (do let w ← actualEmbed u;trace.value 5#u16 i w;tail)=tail := by
  simp only [actualEmbed,AspisS1M31Embedding.Total.embed_total,bind_tc_ok,trace.value]

theorem indexUnused_total {A : Type} (q : Array U32 22#usize) (i : Usize)
    (hi : i.val<22) (tail : Result A) : (do let _ ← Array.index_usize q i;tail)=tail := by
  have bound : i.val<q.val.length := by rw [q.property];exact hi
  obtain ⟨u,read,_⟩ := WP.spec_imp_exists (Array.index_usize_spec q i bound)
  rw [read,bind_tc_ok]

def tracedTail {H : Type} (q : Array U32 22#usize) (self1 : transcript.Transcript H)
    (state7 : Array U8 32#usize) :
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
    let u ← Array.index_usize q 0#usize
    let we ← actualEmbed u
    trace.value 5#u16 0#usize we
    let u1 ← Array.index_usize q 1#usize
    let we1 ← actualEmbed u1
    trace.value 5#u16 1#usize we1
    let u2 ← Array.index_usize q 2#usize
    let we2 ← actualEmbed u2
    trace.value 5#u16 2#usize we2
    let u3 ← Array.index_usize q 3#usize
    let we3 ← actualEmbed u3
    trace.value 5#u16 3#usize we3
    let u4 ← Array.index_usize q 4#usize
    let we4 ← actualEmbed u4
    trace.value 5#u16 4#usize we4
    let u5 ← Array.index_usize q 5#usize
    let we5 ← actualEmbed u5
    trace.value 5#u16 5#usize we5
    let u6 ← Array.index_usize q 6#usize
    let we6 ← actualEmbed u6
    trace.value 5#u16 6#usize we6
    let u7 ← Array.index_usize q 7#usize
    let we7 ← actualEmbed u7
    trace.value 5#u16 7#usize we7
    let u8 ← Array.index_usize q 8#usize
    let we8 ← actualEmbed u8
    trace.value 5#u16 8#usize we8
    let u9 ← Array.index_usize q 9#usize
    let we9 ← actualEmbed u9
    trace.value 5#u16 9#usize we9
    let u10 ← Array.index_usize q 10#usize
    let we10 ← actualEmbed u10
    trace.value 5#u16 10#usize we10
    let u11 ← Array.index_usize q 11#usize
    let we11 ← actualEmbed u11
    trace.value 5#u16 11#usize we11
    let u12 ← Array.index_usize q 12#usize
    let we12 ← actualEmbed u12
    trace.value 5#u16 12#usize we12
    let u13 ← Array.index_usize q 13#usize
    let we13 ← actualEmbed u13
    trace.value 5#u16 13#usize we13
    let u14 ← Array.index_usize q 14#usize
    let we14 ← actualEmbed u14
    trace.value 5#u16 14#usize we14
    let u15 ← Array.index_usize q 15#usize
    let we15 ← actualEmbed u15
    trace.value 5#u16 15#usize we15
    let u16 ← Array.index_usize q 16#usize
    let we16 ← actualEmbed u16
    trace.value 5#u16 16#usize we16
    let u17 ← Array.index_usize q 17#usize
    let we17 ← actualEmbed u17
    trace.value 5#u16 17#usize we17
    let u18 ← Array.index_usize q 18#usize
    let we18 ← actualEmbed u18
    trace.value 5#u16 18#usize we18
    let u19 ← Array.index_usize q 19#usize
    let we19 ← actualEmbed u19
    trace.value 5#u16 19#usize we19
    let u20 ← Array.index_usize q 20#usize
    let we20 ← actualEmbed u20
    trace.value 5#u16 20#usize we20
    let u21 ← Array.index_usize q 21#usize
    let we21 ← actualEmbed u21
    trace.value 5#u16 21#usize we21
    ok (core.result.Result.Ok q, { self1 with state := state7 })

theorem tracedTail_total {H : Type} (q : Array U32 22#usize) (self1 : transcript.Transcript H)
    (state7 : Array U8 32#usize) : tracedTail q self1 state7=
      ok (core.result.Result.Ok q,{self1 with state:=state7}) := by
  unfold tracedTail
  simp (disch := decide) only [embedTrace_total,indexUnused_total]

def queriesWithTrace (B : QueriesModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result ((core.result.Result (Array Std.U32 22#usize) verifier.Error) ×
    (transcript.Transcript H))
  := do
  let self1 ←
    transcript.Transcript.absorb aspis_coreDigest32Inst self row payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← lift (Array.to_slice self1.state)
  let s1 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let a1 ← aspis_coreDigest32Inst.digest self1.hash s2
  let (_, index_mut_back) ← Array.index_mut_usize blocks 0#usize
  let s3 ← lift (Array.to_slice self1.state)
  let s4 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a2 ← aspis_coreDigest32Inst.digest self1.hash s5
  let blocks1 := index_mut_back a2
  let state ← Array.index_usize blocks1 0#usize
  let s6 ← lift (Array.to_slice state)
  let s7 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
  let a3 ← aspis_coreDigest32Inst.digest self1.hash s8
  let blocks2 := index_mut_back a1
  let blocks3 ← Array.update blocks2 1#usize a3
  let s9 ← lift (Array.to_slice state)
  let s10 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s11 ← lift (Array.to_slice (Array.make 2#usize [ s9, s10 ]))
  let a4 ← aspis_coreDigest32Inst.digest self1.hash s11
  let blocks4 ← Array.update blocks1 1#usize a4
  let state1 ← Array.index_usize blocks4 1#usize
  let s12 ← lift (Array.to_slice state1)
  let s13 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s14 ← lift (Array.to_slice (Array.make 2#usize [ s12, s13 ]))
  let a5 ← aspis_coreDigest32Inst.digest self1.hash s14
  let blocks5 ← Array.update blocks3 2#usize a5
  let s15 ← lift (Array.to_slice state1)
  let s16 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s17 ← lift (Array.to_slice (Array.make 2#usize [ s15, s16 ]))
  let a6 ← aspis_coreDigest32Inst.digest self1.hash s17
  let blocks6 ← Array.update blocks4 2#usize a6
  let state2 ← Array.index_usize blocks6 2#usize
  let s18 ← lift (Array.to_slice state2)
  let s19 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s20 ← lift (Array.to_slice (Array.make 2#usize [ s18, s19 ]))
  let a7 ← aspis_coreDigest32Inst.digest self1.hash s20
  let blocks7 ← Array.update blocks5 3#usize a7
  let s21 ← lift (Array.to_slice state2)
  let s22 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s23 ← lift (Array.to_slice (Array.make 2#usize [ s21, s22 ]))
  let a8 ← aspis_coreDigest32Inst.digest self1.hash s23
  let blocks8 ← Array.update blocks6 3#usize a8
  let state3 ← Array.index_usize blocks8 3#usize
  let s24 ← lift (Array.to_slice state3)
  let s25 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s26 ← lift (Array.to_slice (Array.make 2#usize [ s24, s25 ]))
  let a9 ← aspis_coreDigest32Inst.digest self1.hash s26
  let blocks9 ← Array.update blocks7 4#usize a9
  let s27 ← lift (Array.to_slice state3)
  let s28 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s29 ← lift (Array.to_slice (Array.make 2#usize [ s27, s28 ]))
  let a10 ← aspis_coreDigest32Inst.digest self1.hash s29
  let blocks10 ← Array.update blocks8 4#usize a10
  let state4 ← Array.index_usize blocks10 4#usize
  let s30 ← lift (Array.to_slice state4)
  let s31 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s32 ← lift (Array.to_slice (Array.make 2#usize [ s30, s31 ]))
  let a11 ← aspis_coreDigest32Inst.digest self1.hash s32
  let blocks11 ← Array.update blocks9 5#usize a11
  let s33 ← lift (Array.to_slice state4)
  let s34 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s35 ← lift (Array.to_slice (Array.make 2#usize [ s33, s34 ]))
  let a12 ← aspis_coreDigest32Inst.digest self1.hash s35
  let blocks12 ← Array.update blocks10 5#usize a12
  let state5 ← Array.index_usize blocks12 5#usize
  let s36 ← lift (Array.to_slice state5)
  let s37 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s38 ← lift (Array.to_slice (Array.make 2#usize [ s36, s37 ]))
  let a13 ← aspis_coreDigest32Inst.digest self1.hash s38
  let blocks13 ← Array.update blocks11 6#usize a13
  let s39 ← lift (Array.to_slice state5)
  let s40 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s41 ← lift (Array.to_slice (Array.make 2#usize [ s39, s40 ]))
  let a14 ← aspis_coreDigest32Inst.digest self1.hash s41
  let blocks14 ← Array.update blocks12 6#usize a14
  let state6 ← Array.index_usize blocks14 6#usize
  let s42 ← lift (Array.to_slice state6)
  let s43 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s44 ← lift (Array.to_slice (Array.make 2#usize [ s42, s43 ]))
  let a15 ← aspis_coreDigest32Inst.digest self1.hash s44
  let blocks15 ← Array.update blocks13 7#usize a15
  let s45 ← lift (Array.to_slice state6)
  let s46 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s47 ← lift (Array.to_slice (Array.make 2#usize [ s45, s46 ]))
  let a16 ← aspis_coreDigest32Inst.digest self1.hash s47
  let blocks16 ← Array.update blocks14 7#usize a16
  let _ ← Array.index_usize blocks16 7#usize
  let r ← B.decode blocks15 blocks16
  let r1 ←
    core.result.Result.map_err
      (transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (q, state7) := val
    tracedTail q self1 state7
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U32 22#usize) (core.convert.FromSame verifier.Error)
        residual
    ok (r2, self1)

def queriesWithoutTrace (B : QueriesModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (self : transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Result ((core.result.Result (Array Std.U32 22#usize) verifier.Error) ×
    (transcript.Transcript H))
  := do
  let self1 ←
    transcript.Transcript.absorb aspis_coreDigest32Inst self row payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← lift (Array.to_slice self1.state)
  let s1 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s2 ← lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))
  let a1 ← aspis_coreDigest32Inst.digest self1.hash s2
  let (_, index_mut_back) ← Array.index_mut_usize blocks 0#usize
  let s3 ← lift (Array.to_slice self1.state)
  let s4 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s5 ← lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))
  let a2 ← aspis_coreDigest32Inst.digest self1.hash s5
  let blocks1 := index_mut_back a2
  let state ← Array.index_usize blocks1 0#usize
  let s6 ← lift (Array.to_slice state)
  let s7 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s8 ← lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))
  let a3 ← aspis_coreDigest32Inst.digest self1.hash s8
  let blocks2 := index_mut_back a1
  let blocks3 ← Array.update blocks2 1#usize a3
  let s9 ← lift (Array.to_slice state)
  let s10 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s11 ← lift (Array.to_slice (Array.make 2#usize [ s9, s10 ]))
  let a4 ← aspis_coreDigest32Inst.digest self1.hash s11
  let blocks4 ← Array.update blocks1 1#usize a4
  let state1 ← Array.index_usize blocks4 1#usize
  let s12 ← lift (Array.to_slice state1)
  let s13 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s14 ← lift (Array.to_slice (Array.make 2#usize [ s12, s13 ]))
  let a5 ← aspis_coreDigest32Inst.digest self1.hash s14
  let blocks5 ← Array.update blocks3 2#usize a5
  let s15 ← lift (Array.to_slice state1)
  let s16 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s17 ← lift (Array.to_slice (Array.make 2#usize [ s15, s16 ]))
  let a6 ← aspis_coreDigest32Inst.digest self1.hash s17
  let blocks6 ← Array.update blocks4 2#usize a6
  let state2 ← Array.index_usize blocks6 2#usize
  let s18 ← lift (Array.to_slice state2)
  let s19 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s20 ← lift (Array.to_slice (Array.make 2#usize [ s18, s19 ]))
  let a7 ← aspis_coreDigest32Inst.digest self1.hash s20
  let blocks7 ← Array.update blocks5 3#usize a7
  let s21 ← lift (Array.to_slice state2)
  let s22 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s23 ← lift (Array.to_slice (Array.make 2#usize [ s21, s22 ]))
  let a8 ← aspis_coreDigest32Inst.digest self1.hash s23
  let blocks8 ← Array.update blocks6 3#usize a8
  let state3 ← Array.index_usize blocks8 3#usize
  let s24 ← lift (Array.to_slice state3)
  let s25 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s26 ← lift (Array.to_slice (Array.make 2#usize [ s24, s25 ]))
  let a9 ← aspis_coreDigest32Inst.digest self1.hash s26
  let blocks9 ← Array.update blocks7 4#usize a9
  let s27 ← lift (Array.to_slice state3)
  let s28 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s29 ← lift (Array.to_slice (Array.make 2#usize [ s27, s28 ]))
  let a10 ← aspis_coreDigest32Inst.digest self1.hash s29
  let blocks10 ← Array.update blocks8 4#usize a10
  let state4 ← Array.index_usize blocks10 4#usize
  let s30 ← lift (Array.to_slice state4)
  let s31 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s32 ← lift (Array.to_slice (Array.make 2#usize [ s30, s31 ]))
  let a11 ← aspis_coreDigest32Inst.digest self1.hash s32
  let blocks11 ← Array.update blocks9 5#usize a11
  let s33 ← lift (Array.to_slice state4)
  let s34 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s35 ← lift (Array.to_slice (Array.make 2#usize [ s33, s34 ]))
  let a12 ← aspis_coreDigest32Inst.digest self1.hash s35
  let blocks12 ← Array.update blocks10 5#usize a12
  let state5 ← Array.index_usize blocks12 5#usize
  let s36 ← lift (Array.to_slice state5)
  let s37 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s38 ← lift (Array.to_slice (Array.make 2#usize [ s36, s37 ]))
  let a13 ← aspis_coreDigest32Inst.digest self1.hash s38
  let blocks13 ← Array.update blocks11 6#usize a13
  let s39 ← lift (Array.to_slice state5)
  let s40 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s41 ← lift (Array.to_slice (Array.make 2#usize [ s39, s40 ]))
  let a14 ← aspis_coreDigest32Inst.digest self1.hash s41
  let blocks14 ← Array.update blocks12 6#usize a14
  let state6 ← Array.index_usize blocks14 6#usize
  let s42 ← lift (Array.to_slice state6)
  let s43 ← lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))
  let s44 ← lift (Array.to_slice (Array.make 2#usize [ s42, s43 ]))
  let a15 ← aspis_coreDigest32Inst.digest self1.hash s44
  let blocks15 ← Array.update blocks13 7#usize a15
  let s45 ← lift (Array.to_slice state6)
  let s46 ← lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))
  let s47 ← lift (Array.to_slice (Array.make 2#usize [ s45, s46 ]))
  let a16 ← aspis_coreDigest32Inst.digest self1.hash s47
  let blocks16 ← Array.update blocks14 7#usize a16
  let _ ← Array.index_usize blocks16 7#usize
  let r ← B.decode blocks15 blocks16
  let r1 ←
    core.result.Result.map_err
      (transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (q, state7) := val
    ok (core.result.Result.Ok q, { self1 with state := state7 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U32 22#usize) (core.convert.FromSame verifier.Error)
        residual
    ok (r2, self1)


/-- COMPLETE Result identity: actual default-release trace embeddings cannot
introduce failure/divergence or change the selected queries/transcript state.
All original absorb/digest/decode/rejection paths remain, with no successful
caller, digest-totality, scan-totality or embedding-law premise. -/
theorem queries_actual_embed {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    QueriesModel.queries {B with embed:=actualEmbed} D self row payload=
      queriesWithoutTrace B D self row payload := by
  unfold QueriesModel.queries queriesWithoutTrace
  simp (disch := decide) only [embedTrace_total,indexUnused_total]

#print axioms embedTrace_total
#print axioms indexUnused_total
#print axioms tracedTail_total
#print axioms queries_actual_embed
end AspisR1PublicPreparation.S1QueryTraceEmbedding
