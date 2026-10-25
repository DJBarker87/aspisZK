import F3K_CodeStep
import F3K_AbsorbCode
import F3K_ArrayFacts
import F3J_QueryPairs
import S1PreparedQueryEffectsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
namespace AspisR1.F3K_QueryCode
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
/-- Successful installed query Code records all sixteen pairs after its absorber. -/
theorem observed {H : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self 31#u8 payload=ok (.Ok out,after)) :
    ∃ absorbed calls,
      transcript.Transcript.absorb D self 31#u8 payload=ok absorbed ∧
      F3J_QueryPairs.Pairs D absorbed.hash 8 absorbed.state calls ∧
      observe (run (PreparedQueryEffects.queries effects B D self 31#u8 payload)).1=
        (flatten (CallerStep.openingAbsorbParts self.state 191#u8
          (UScalar.cast .U32 (Slice.len payload)) payload),decodeState absorbed.state)::
        F3J_QueryPairs.observed calls := by
  unfold QueriesModel.queries at h
  obtain ⟨self1,hcall1,h⟩ := bind_success (transcript.Transcript.absorb D self 31#u8 payload) _ _ h
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
  have state_eq : state = a2 := Result.ok.inj
    (hcall14.symm.trans (F3K_ArrayFacts.mutated blocks 0#usize unused index_mut_back a2 hcall8))
  cases state_eq
  have state1_eq : state1 = a4 := Result.ok.inj
    (hcall26.symm.trans (F3K_ArrayFacts.updated _ _ 1#usize a4 hcall25))
  cases state1_eq
  have state2_eq : state2 = a6 := Result.ok.inj
    (hcall37.symm.trans (F3K_ArrayFacts.updated _ _ 2#usize a6 hcall36))
  cases state2_eq
  have state3_eq : state3 = a8 := Result.ok.inj
    (hcall48.symm.trans (F3K_ArrayFacts.updated _ _ 3#usize a8 hcall47))
  cases state3_eq
  have state4_eq : state4 = a10 := Result.ok.inj
    (hcall59.symm.trans (F3K_ArrayFacts.updated _ _ 4#usize a10 hcall58))
  cases state4_eq
  have state5_eq : state5 = a12 := Result.ok.inj
    (hcall70.symm.trans (F3K_ArrayFacts.updated _ _ 5#usize a12 hcall69))
  cases state5_eq
  have state6_eq : state6 = a14 := Result.ok.inj
    (hcall81.symm.trans (F3K_ArrayFacts.updated _ _ 6#usize a14 hcall80))
  cases state6_eq
  cases Result.ok.inj hcall4
  cases Result.ok.inj hcall5
  cases Result.ok.inj hcall6
  cases Result.ok.inj hcall9
  cases Result.ok.inj hcall10
  cases Result.ok.inj hcall11
  cases Result.ok.inj hcall15
  cases Result.ok.inj hcall16
  cases Result.ok.inj hcall17
  cases Result.ok.inj hcall21
  cases Result.ok.inj hcall22
  cases Result.ok.inj hcall23
  cases Result.ok.inj hcall27
  cases Result.ok.inj hcall28
  cases Result.ok.inj hcall29
  cases Result.ok.inj hcall32
  cases Result.ok.inj hcall33
  cases Result.ok.inj hcall34
  cases Result.ok.inj hcall38
  cases Result.ok.inj hcall39
  cases Result.ok.inj hcall40
  cases Result.ok.inj hcall43
  cases Result.ok.inj hcall44
  cases Result.ok.inj hcall45
  cases Result.ok.inj hcall49
  cases Result.ok.inj hcall50
  cases Result.ok.inj hcall51
  cases Result.ok.inj hcall54
  cases Result.ok.inj hcall55
  cases Result.ok.inj hcall56
  cases Result.ok.inj hcall60
  cases Result.ok.inj hcall61
  cases Result.ok.inj hcall62
  cases Result.ok.inj hcall65
  cases Result.ok.inj hcall66
  cases Result.ok.inj hcall67
  cases Result.ok.inj hcall71
  cases Result.ok.inj hcall72
  cases Result.ok.inj hcall73
  cases Result.ok.inj hcall76
  cases Result.ok.inj hcall77
  cases Result.ok.inj hcall78
  cases Result.ok.inj hcall82
  cases Result.ok.inj hcall83
  cases Result.ok.inj hcall84
  cases Result.ok.inj hcall87
  cases Result.ok.inj hcall88
  cases Result.ok.inj hcall89
  let calls : List F3J_QueryPairs.Call := [(TranscriptStep.readParts self1.state 1#u8,a1),(TranscriptStep.readParts self1.state 2#u8,a2),(TranscriptStep.readParts a2 1#u8,a3),(TranscriptStep.readParts a2 2#u8,a4),(TranscriptStep.readParts a4 1#u8,a5),(TranscriptStep.readParts a4 2#u8,a6),(TranscriptStep.readParts a6 1#u8,a7),(TranscriptStep.readParts a6 2#u8,a8),(TranscriptStep.readParts a8 1#u8,a9),(TranscriptStep.readParts a8 2#u8,a10),(TranscriptStep.readParts a10 1#u8,a11),(TranscriptStep.readParts a10 2#u8,a12),(TranscriptStep.readParts a12 1#u8,a13),(TranscriptStep.readParts a12 2#u8,a14),(TranscriptStep.readParts a14 1#u8,a15),(TranscriptStep.readParts a14 2#u8,a16)]
  refine ⟨self1,calls,hcall1,?_,?_⟩
  · refine F3J_QueryPairs.Pairs.cons hcall7 hcall12 ?_
    refine F3J_QueryPairs.Pairs.cons hcall18 hcall24 ?_
    refine F3J_QueryPairs.Pairs.cons hcall30 hcall35 ?_
    refine F3J_QueryPairs.Pairs.cons hcall41 hcall46 ?_
    refine F3J_QueryPairs.Pairs.cons hcall52 hcall57 ?_
    refine F3J_QueryPairs.Pairs.cons hcall63 hcall68 ?_
    refine F3J_QueryPairs.Pairs.cons hcall74 hcall79 ?_
    refine F3J_QueryPairs.Pairs.cons hcall85 hcall90 ?_
    exact .nil _
  · unfold PreparedQueryEffects.queries
    change observe (run (PreparedHashCode.bind (PreparedHashEffects.absorb effects D self 31#u8 payload) _)).1=_
    rw [F3K_CodeStep.absorb D self self1 payload hcall1]
    change _ = (flatten (CallerStep.openingAbsorbParts self.state 191#u8
      (UScalar.cast .U32 (Slice.len payload)) payload),decodeState self1.state)::
      F3J_QueryPairs.observed calls
    congr 1
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall7]
    erw [F3K_CodeStep.lift_success _ _ hcall8]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall12]
    erw [F3K_CodeStep.lift_success _ _ hcall14]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall18]
    erw [F3K_CodeStep.lift_success _ _ hcall20]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall24]
    erw [F3K_CodeStep.lift_success _ _ hcall25]
    erw [F3K_CodeStep.lift_success _ _ hcall26]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall30]
    erw [F3K_CodeStep.lift_success _ _ hcall31]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall35]
    erw [F3K_CodeStep.lift_success _ _ hcall36]
    erw [F3K_CodeStep.lift_success _ _ hcall37]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall41]
    erw [F3K_CodeStep.lift_success _ _ hcall42]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall46]
    erw [F3K_CodeStep.lift_success _ _ hcall47]
    erw [F3K_CodeStep.lift_success _ _ hcall48]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall52]
    erw [F3K_CodeStep.lift_success _ _ hcall53]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall57]
    erw [F3K_CodeStep.lift_success _ _ hcall58]
    erw [F3K_CodeStep.lift_success _ _ hcall59]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall63]
    erw [F3K_CodeStep.lift_success _ _ hcall64]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall68]
    erw [F3K_CodeStep.lift_success _ _ hcall69]
    erw [F3K_CodeStep.lift_success _ _ hcall70]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall74]
    erw [F3K_CodeStep.lift_success _ _ hcall75]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall79]
    erw [F3K_CodeStep.lift_success _ _ hcall80]
    erw [F3K_CodeStep.lift_success _ _ hcall81]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall85]
    erw [F3K_CodeStep.lift_success _ _ hcall86]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.pure_step]
    erw [F3K_CodeStep.digest_success _ _ _ _ hcall90]
    simp only [Bind.bind,Pure.pure,PreparedHashCode.bind,run,lift,liftM,MonadLift.monadLift,MonadLiftT.monadLift,
      hcall91,hcall92,hcall93,hindex0,hembed0,htrace0,hindex1,hembed1,htrace1,hindex2,hembed2,htrace2,hindex3,hembed3,htrace3,hindex4,hembed4,htrace4,hindex5,hembed5,htrace5,hindex6,hembed6,htrace6,hindex7,hembed7,htrace7,hindex8,hembed8,htrace8,hindex9,hembed9,htrace9,hindex10,hembed10,htrace10,hindex11,hembed11,htrace11,hindex12,hembed12,htrace12,hindex13,hembed13,htrace13,hindex14,hembed14,htrace14,hindex15,hembed15,htrace15,hindex16,hembed16,htrace16,hindex17,hembed17,htrace17,hindex18,hembed18,htrace18,hindex19,hembed19,htrace19,hindex20,hembed20,htrace20,hindex21,hembed21,htrace21,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
      trace.value,observe,List.flatMap_cons,List.flatMap_nil,List.singleton_append,List.append_nil,
      F3J_QueryPairs.observed,calls,List.map_cons,List.map_nil]
    rfl

#print axioms observed
end AspisR1.F3K_QueryCode
