import ExtractedOpeningQueriesModel

open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation

structure DigestCall {H : Type} (D : aspis_core.Digest32 H) (hash : H) where
  state : Array U8 32#usize
  tag : U8
  stateSlice : Slice U8
  tagSlice : Slice U8
  input : Slice (Slice U8)
  output : Array U8 32#usize
  hstate : lift (Array.to_slice state) = ok stateSlice
  htag : lift (Array.to_slice (Array.make 1#usize [tag])) = ok tagSlice
  hinput : lift (Array.to_slice (Array.make 2#usize [stateSlice, tagSlice])) = ok input
  hdigest : D.digest hash input = ok output

structure DigestPair {H : Type} (D : aspis_core.Digest32 H) (hash : H) where
  state : Array U8 32#usize
  squeeze : DigestCall D hash
  advance : DigestCall D hash
  hsqueezeState : squeeze.state = state
  hadvanceState : advance.state = state
  hsqueezeTag : squeeze.tag = 1#u8
  hadvanceTag : advance.tag = 2#u8

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The current extracted query method's successful digest calls, retained as
exact grouped source inputs. No hash-distribution assumption is made. -/
theorem queries_success_with_digest_pairs {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 := by
  unfold QueriesModel.queries at h
  obtain ⟨self1,hcall1,h⟩ := bind_success (transcript.Transcript.absorb D self row payload) _ _ h
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  obtain ⟨s,hcall4,h⟩ := bind_success (lift (Array.to_slice self1.state)) _ _ h
  obtain ⟨s1,hcall5,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s2,hcall6,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s, s1 ]))) _ _ h
  obtain ⟨a1,hcall7,h⟩ := bind_success (D.digest self1.hash s2) _ _ h
  obtain ⟨unused,index_mut_back,hcall8,h⟩ := pair_bind_success (Array.index_mut_usize blocks 0#usize) _ _ h
  obtain ⟨s3,hcall9,h⟩ := bind_success (lift (Array.to_slice self1.state)) _ _ h
  obtain ⟨s4,hcall10,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s5,hcall11,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s3, s4 ]))) _ _ h
  obtain ⟨a2,hcall12,h⟩ := bind_success (D.digest self1.hash s5) _ _ h
  let blocks1 := index_mut_back a2
  obtain ⟨state,hcall14,h⟩ := bind_success (Array.index_usize blocks1 0#usize) _ _ h
  obtain ⟨s6,hcall15,h⟩ := bind_success (lift (Array.to_slice state)) _ _ h
  obtain ⟨s7,hcall16,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s8,hcall17,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s6, s7 ]))) _ _ h
  obtain ⟨a3,hcall18,h⟩ := bind_success (D.digest self1.hash s8) _ _ h
  let blocks2 := index_mut_back a1
  obtain ⟨blocks3,hcall20,h⟩ := bind_success (Array.update blocks2 1#usize a3) _ _ h
  obtain ⟨s9,hcall21,h⟩ := bind_success (lift (Array.to_slice state)) _ _ h
  obtain ⟨s10,hcall22,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s11,hcall23,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s9, s10 ]))) _ _ h
  obtain ⟨a4,hcall24,h⟩ := bind_success (D.digest self1.hash s11) _ _ h
  obtain ⟨blocks4,hcall25,h⟩ := bind_success (Array.update blocks1 1#usize a4) _ _ h
  obtain ⟨state1,hcall26,h⟩ := bind_success (Array.index_usize blocks4 1#usize) _ _ h
  obtain ⟨s12,hcall27,h⟩ := bind_success (lift (Array.to_slice state1)) _ _ h
  obtain ⟨s13,hcall28,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s14,hcall29,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s12, s13 ]))) _ _ h
  obtain ⟨a5,hcall30,h⟩ := bind_success (D.digest self1.hash s14) _ _ h
  obtain ⟨blocks5,hcall31,h⟩ := bind_success (Array.update blocks3 2#usize a5) _ _ h
  obtain ⟨s15,hcall32,h⟩ := bind_success (lift (Array.to_slice state1)) _ _ h
  obtain ⟨s16,hcall33,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s17,hcall34,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s15, s16 ]))) _ _ h
  obtain ⟨a6,hcall35,h⟩ := bind_success (D.digest self1.hash s17) _ _ h
  obtain ⟨blocks6,hcall36,h⟩ := bind_success (Array.update blocks4 2#usize a6) _ _ h
  obtain ⟨state2,hcall37,h⟩ := bind_success (Array.index_usize blocks6 2#usize) _ _ h
  obtain ⟨s18,hcall38,h⟩ := bind_success (lift (Array.to_slice state2)) _ _ h
  obtain ⟨s19,hcall39,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s20,hcall40,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s18, s19 ]))) _ _ h
  obtain ⟨a7,hcall41,h⟩ := bind_success (D.digest self1.hash s20) _ _ h
  obtain ⟨blocks7,hcall42,h⟩ := bind_success (Array.update blocks5 3#usize a7) _ _ h
  obtain ⟨s21,hcall43,h⟩ := bind_success (lift (Array.to_slice state2)) _ _ h
  obtain ⟨s22,hcall44,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s23,hcall45,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s21, s22 ]))) _ _ h
  obtain ⟨a8,hcall46,h⟩ := bind_success (D.digest self1.hash s23) _ _ h
  obtain ⟨blocks8,hcall47,h⟩ := bind_success (Array.update blocks6 3#usize a8) _ _ h
  obtain ⟨state3,hcall48,h⟩ := bind_success (Array.index_usize blocks8 3#usize) _ _ h
  obtain ⟨s24,hcall49,h⟩ := bind_success (lift (Array.to_slice state3)) _ _ h
  obtain ⟨s25,hcall50,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s26,hcall51,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s24, s25 ]))) _ _ h
  obtain ⟨a9,hcall52,h⟩ := bind_success (D.digest self1.hash s26) _ _ h
  obtain ⟨blocks9,hcall53,h⟩ := bind_success (Array.update blocks7 4#usize a9) _ _ h
  obtain ⟨s27,hcall54,h⟩ := bind_success (lift (Array.to_slice state3)) _ _ h
  obtain ⟨s28,hcall55,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s29,hcall56,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s27, s28 ]))) _ _ h
  obtain ⟨a10,hcall57,h⟩ := bind_success (D.digest self1.hash s29) _ _ h
  obtain ⟨blocks10,hcall58,h⟩ := bind_success (Array.update blocks8 4#usize a10) _ _ h
  obtain ⟨state4,hcall59,h⟩ := bind_success (Array.index_usize blocks10 4#usize) _ _ h
  obtain ⟨s30,hcall60,h⟩ := bind_success (lift (Array.to_slice state4)) _ _ h
  obtain ⟨s31,hcall61,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s32,hcall62,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s30, s31 ]))) _ _ h
  obtain ⟨a11,hcall63,h⟩ := bind_success (D.digest self1.hash s32) _ _ h
  obtain ⟨blocks11,hcall64,h⟩ := bind_success (Array.update blocks9 5#usize a11) _ _ h
  obtain ⟨s33,hcall65,h⟩ := bind_success (lift (Array.to_slice state4)) _ _ h
  obtain ⟨s34,hcall66,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s35,hcall67,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s33, s34 ]))) _ _ h
  obtain ⟨a12,hcall68,h⟩ := bind_success (D.digest self1.hash s35) _ _ h
  obtain ⟨blocks12,hcall69,h⟩ := bind_success (Array.update blocks10 5#usize a12) _ _ h
  obtain ⟨state5,hcall70,h⟩ := bind_success (Array.index_usize blocks12 5#usize) _ _ h
  obtain ⟨s36,hcall71,h⟩ := bind_success (lift (Array.to_slice state5)) _ _ h
  obtain ⟨s37,hcall72,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s38,hcall73,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s36, s37 ]))) _ _ h
  obtain ⟨a13,hcall74,h⟩ := bind_success (D.digest self1.hash s38) _ _ h
  obtain ⟨blocks13,hcall75,h⟩ := bind_success (Array.update blocks11 6#usize a13) _ _ h
  obtain ⟨s39,hcall76,h⟩ := bind_success (lift (Array.to_slice state5)) _ _ h
  obtain ⟨s40,hcall77,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s41,hcall78,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s39, s40 ]))) _ _ h
  obtain ⟨a14,hcall79,h⟩ := bind_success (D.digest self1.hash s41) _ _ h
  obtain ⟨blocks14,hcall80,h⟩ := bind_success (Array.update blocks12 6#usize a14) _ _ h
  obtain ⟨state6,hcall81,h⟩ := bind_success (Array.index_usize blocks14 6#usize) _ _ h
  obtain ⟨s42,hcall82,h⟩ := bind_success (lift (Array.to_slice state6)) _ _ h
  obtain ⟨s43,hcall83,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 1#u8 ]))) _ _ h
  obtain ⟨s44,hcall84,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s42, s43 ]))) _ _ h
  obtain ⟨a15,hcall85,h⟩ := bind_success (D.digest self1.hash s44) _ _ h
  obtain ⟨blocks15,hcall86,h⟩ := bind_success (Array.update blocks13 7#usize a15) _ _ h
  obtain ⟨s45,hcall87,h⟩ := bind_success (lift (Array.to_slice state6)) _ _ h
  obtain ⟨s46,hcall88,h⟩ := bind_success (lift (Array.to_slice (Array.make 1#usize [ 2#u8 ]))) _ _ h
  obtain ⟨s47,hcall89,h⟩ := bind_success (lift (Array.to_slice (Array.make 2#usize [ s45, s46 ]))) _ _ h
  obtain ⟨a16,hcall90,h⟩ := bind_success (D.digest self1.hash s47) _ _ h
  obtain ⟨blocks16,hcall91,h⟩ := bind_success (Array.update blocks14 7#usize a16) _ _ h
  obtain ⟨unusedLast,hcall92,h⟩ := bind_success (Array.index_usize blocks16 7#usize) _ _ h
  obtain ⟨r,hcall93,h⟩ := bind_success (B.decode blocks15 blocks16) _ _ h
  have hok : ∃ value, r = core.result.Result.Ok value := by
    cases r with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
      simp only [core.result.Result.map_err,
        transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError,
        transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
  obtain ⟨tuple,rfl⟩ := hok
  obtain ⟨q,selected⟩ := tuple
  simp only [core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
  obtain ⟨u,hindex0,h⟩ := bind_success (Array.index_usize q 0#usize) _ _ h
  obtain ⟨we,hembed0,h⟩ := bind_success (B.embed u) _ _ h
  obtain ⟨mark0,htrace0,h⟩ := bind_success (trace.value 5#u16 0#usize we) _ _ h
  cases mark0
  obtain ⟨u1,hindex1,h⟩ := bind_success (Array.index_usize q 1#usize) _ _ h
  obtain ⟨we1,hembed1,h⟩ := bind_success (B.embed u1) _ _ h
  obtain ⟨mark1,htrace1,h⟩ := bind_success (trace.value 5#u16 1#usize we1) _ _ h
  cases mark1
  obtain ⟨u2,hindex2,h⟩ := bind_success (Array.index_usize q 2#usize) _ _ h
  obtain ⟨we2,hembed2,h⟩ := bind_success (B.embed u2) _ _ h
  obtain ⟨mark2,htrace2,h⟩ := bind_success (trace.value 5#u16 2#usize we2) _ _ h
  cases mark2
  obtain ⟨u3,hindex3,h⟩ := bind_success (Array.index_usize q 3#usize) _ _ h
  obtain ⟨we3,hembed3,h⟩ := bind_success (B.embed u3) _ _ h
  obtain ⟨mark3,htrace3,h⟩ := bind_success (trace.value 5#u16 3#usize we3) _ _ h
  cases mark3
  obtain ⟨u4,hindex4,h⟩ := bind_success (Array.index_usize q 4#usize) _ _ h
  obtain ⟨we4,hembed4,h⟩ := bind_success (B.embed u4) _ _ h
  obtain ⟨mark4,htrace4,h⟩ := bind_success (trace.value 5#u16 4#usize we4) _ _ h
  cases mark4
  obtain ⟨u5,hindex5,h⟩ := bind_success (Array.index_usize q 5#usize) _ _ h
  obtain ⟨we5,hembed5,h⟩ := bind_success (B.embed u5) _ _ h
  obtain ⟨mark5,htrace5,h⟩ := bind_success (trace.value 5#u16 5#usize we5) _ _ h
  cases mark5
  obtain ⟨u6,hindex6,h⟩ := bind_success (Array.index_usize q 6#usize) _ _ h
  obtain ⟨we6,hembed6,h⟩ := bind_success (B.embed u6) _ _ h
  obtain ⟨mark6,htrace6,h⟩ := bind_success (trace.value 5#u16 6#usize we6) _ _ h
  cases mark6
  obtain ⟨u7,hindex7,h⟩ := bind_success (Array.index_usize q 7#usize) _ _ h
  obtain ⟨we7,hembed7,h⟩ := bind_success (B.embed u7) _ _ h
  obtain ⟨mark7,htrace7,h⟩ := bind_success (trace.value 5#u16 7#usize we7) _ _ h
  cases mark7
  obtain ⟨u8,hindex8,h⟩ := bind_success (Array.index_usize q 8#usize) _ _ h
  obtain ⟨we8,hembed8,h⟩ := bind_success (B.embed u8) _ _ h
  obtain ⟨mark8,htrace8,h⟩ := bind_success (trace.value 5#u16 8#usize we8) _ _ h
  cases mark8
  obtain ⟨u9,hindex9,h⟩ := bind_success (Array.index_usize q 9#usize) _ _ h
  obtain ⟨we9,hembed9,h⟩ := bind_success (B.embed u9) _ _ h
  obtain ⟨mark9,htrace9,h⟩ := bind_success (trace.value 5#u16 9#usize we9) _ _ h
  cases mark9
  obtain ⟨u10,hindex10,h⟩ := bind_success (Array.index_usize q 10#usize) _ _ h
  obtain ⟨we10,hembed10,h⟩ := bind_success (B.embed u10) _ _ h
  obtain ⟨mark10,htrace10,h⟩ := bind_success (trace.value 5#u16 10#usize we10) _ _ h
  cases mark10
  obtain ⟨u11,hindex11,h⟩ := bind_success (Array.index_usize q 11#usize) _ _ h
  obtain ⟨we11,hembed11,h⟩ := bind_success (B.embed u11) _ _ h
  obtain ⟨mark11,htrace11,h⟩ := bind_success (trace.value 5#u16 11#usize we11) _ _ h
  cases mark11
  obtain ⟨u12,hindex12,h⟩ := bind_success (Array.index_usize q 12#usize) _ _ h
  obtain ⟨we12,hembed12,h⟩ := bind_success (B.embed u12) _ _ h
  obtain ⟨mark12,htrace12,h⟩ := bind_success (trace.value 5#u16 12#usize we12) _ _ h
  cases mark12
  obtain ⟨u13,hindex13,h⟩ := bind_success (Array.index_usize q 13#usize) _ _ h
  obtain ⟨we13,hembed13,h⟩ := bind_success (B.embed u13) _ _ h
  obtain ⟨mark13,htrace13,h⟩ := bind_success (trace.value 5#u16 13#usize we13) _ _ h
  cases mark13
  obtain ⟨u14,hindex14,h⟩ := bind_success (Array.index_usize q 14#usize) _ _ h
  obtain ⟨we14,hembed14,h⟩ := bind_success (B.embed u14) _ _ h
  obtain ⟨mark14,htrace14,h⟩ := bind_success (trace.value 5#u16 14#usize we14) _ _ h
  cases mark14
  obtain ⟨u15,hindex15,h⟩ := bind_success (Array.index_usize q 15#usize) _ _ h
  obtain ⟨we15,hembed15,h⟩ := bind_success (B.embed u15) _ _ h
  obtain ⟨mark15,htrace15,h⟩ := bind_success (trace.value 5#u16 15#usize we15) _ _ h
  cases mark15
  obtain ⟨u16,hindex16,h⟩ := bind_success (Array.index_usize q 16#usize) _ _ h
  obtain ⟨we16,hembed16,h⟩ := bind_success (B.embed u16) _ _ h
  obtain ⟨mark16,htrace16,h⟩ := bind_success (trace.value 5#u16 16#usize we16) _ _ h
  cases mark16
  obtain ⟨u17,hindex17,h⟩ := bind_success (Array.index_usize q 17#usize) _ _ h
  obtain ⟨we17,hembed17,h⟩ := bind_success (B.embed u17) _ _ h
  obtain ⟨mark17,htrace17,h⟩ := bind_success (trace.value 5#u16 17#usize we17) _ _ h
  cases mark17
  obtain ⟨u18,hindex18,h⟩ := bind_success (Array.index_usize q 18#usize) _ _ h
  obtain ⟨we18,hembed18,h⟩ := bind_success (B.embed u18) _ _ h
  obtain ⟨mark18,htrace18,h⟩ := bind_success (trace.value 5#u16 18#usize we18) _ _ h
  cases mark18
  obtain ⟨u19,hindex19,h⟩ := bind_success (Array.index_usize q 19#usize) _ _ h
  obtain ⟨we19,hembed19,h⟩ := bind_success (B.embed u19) _ _ h
  obtain ⟨mark19,htrace19,h⟩ := bind_success (trace.value 5#u16 19#usize we19) _ _ h
  cases mark19
  obtain ⟨u20,hindex20,h⟩ := bind_success (Array.index_usize q 20#usize) _ _ h
  obtain ⟨we20,hembed20,h⟩ := bind_success (B.embed u20) _ _ h
  obtain ⟨mark20,htrace20,h⟩ := bind_success (trace.value 5#u16 20#usize we20) _ _ h
  cases mark20
  obtain ⟨u21,hindex21,h⟩ := bind_success (Array.index_usize q 21#usize) _ _ h
  obtain ⟨we21,hembed21,h⟩ := bind_success (B.embed u21) _ _ h
  obtain ⟨mark21,htrace21,h⟩ := bind_success (trace.value 5#u16 21#usize we21) _ _ h
  cases mark21
  have he := Result.ok.inj h
  have hq : q = out := core.result.Result.Ok.inj (congrArg Prod.fst he)
  have ha : after = {self1 with state := selected} := (congrArg Prod.snd he).symm
  have hdecode : B.decode blocks15 blocks16 = ok (.Ok (out, selected)) := by
    simpa only [hq] using hcall93
  refine ⟨self1, blocks15, blocks16, selected, ?_⟩
  refine ⟨[
    (⟨self1.state, ⟨self1.state, 1#u8, s, s1, s2, a1, hcall4, hcall5, hcall6, hcall7⟩, ⟨self1.state, 2#u8, s3, s4, s5, a2, hcall9, hcall10, hcall11, hcall12⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state, ⟨state, 1#u8, s6, s7, s8, a3, hcall15, hcall16, hcall17, hcall18⟩, ⟨state, 2#u8, s9, s10, s11, a4, hcall21, hcall22, hcall23, hcall24⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state1, ⟨state1, 1#u8, s12, s13, s14, a5, hcall27, hcall28, hcall29, hcall30⟩, ⟨state1, 2#u8, s15, s16, s17, a6, hcall32, hcall33, hcall34, hcall35⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state2, ⟨state2, 1#u8, s18, s19, s20, a7, hcall38, hcall39, hcall40, hcall41⟩, ⟨state2, 2#u8, s21, s22, s23, a8, hcall43, hcall44, hcall45, hcall46⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state3, ⟨state3, 1#u8, s24, s25, s26, a9, hcall49, hcall50, hcall51, hcall52⟩, ⟨state3, 2#u8, s27, s28, s29, a10, hcall54, hcall55, hcall56, hcall57⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state4, ⟨state4, 1#u8, s30, s31, s32, a11, hcall60, hcall61, hcall62, hcall63⟩, ⟨state4, 2#u8, s33, s34, s35, a12, hcall65, hcall66, hcall67, hcall68⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state5, ⟨state5, 1#u8, s36, s37, s38, a13, hcall71, hcall72, hcall73, hcall74⟩, ⟨state5, 2#u8, s39, s40, s41, a14, hcall76, hcall77, hcall78, hcall79⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash),
    (⟨state6, ⟨state6, 1#u8, s42, s43, s44, a15, hcall82, hcall83, hcall84, hcall85⟩, ⟨state6, 2#u8, s45, s46, s47, a16, hcall87, hcall88, hcall89, hcall90⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  ], ?_⟩
  exact ⟨hcall1, hdecode, ha, rfl⟩

#print axioms queries_success_with_digest_pairs
end AspisR1PublicPreparation.Query31SourceSchedule
end
