import ExtractedOpeningQueriesModel
import Query31ArrayReadback
import Lean.Elab.Tactic.Omega

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

def stateChain {H : Type} {D : aspis_core.Digest32 H} {hash : H} :
    List (DigestPair D hash) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      second.state = first.advance.output ∧ stateChain (second :: rest)

/-- Each digest pair is exactly the byte pair stored at its source array slot
and supplied to the retained decoder. -/
private theorem small_nat_usize (n : Nat) (hn : n < 8) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 8 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

def index8 (i : Nat) (hi : i < 8) : Usize :=
  Usize.ofNatCore i (small_nat_usize i hi)

private theorem index8_zero (h : 0 < 8) :
    index8 0 h = 0#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_one (h : 1 < 8) :
    index8 1 h = 1#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_two (h : 2 < 8) :
    index8 2 h = 2#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_three (h : 3 < 8) :
    index8 3 h = 3#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_four (h : 4 < 8) :
    index8 4 h = 4#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_five (h : 5 < 8) :
    index8 5 h = 5#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_six (h : 6 < 8) :
    index8 6 h = 6#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]
private theorem index8_seven (h : 7 < 8) :
    index8 7 h = 7#usize := by
  apply UScalar.eq_of_val_eq
  simp [index8, UScalar.ofNatCore_val_eq]

def materializedOutputs {H : Type} {D : aspis_core.Digest32 H} {hash : H}
    (pairs : List (DigestPair D hash))
    (blocks advances : Array (Array U8 32#usize) 8#usize) : Prop :=
  ∀ (i : Nat) (hi : i < 8),
    ∃ pair, pairs[i]? = some pair ∧
      Array.index_usize blocks (index8 i hi) = ok pair.squeeze.output ∧
      Array.index_usize advances (index8 i hi) = ok pair.advance.output

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
theorem queries_success_with_digest_pairs_full {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        (∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧
        stateChain pairs ∧ materializedOutputs pairs blocks advances := by
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
  let pair0 : DigestPair D self1.hash := (⟨self1.state, ⟨self1.state, 1#u8, s, s1, s2, a1, hcall4, hcall5, hcall6, hcall7⟩, ⟨self1.state, 2#u8, s3, s4, s5, a2, hcall9, hcall10, hcall11, hcall12⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair1 : DigestPair D self1.hash := (⟨state, ⟨state, 1#u8, s6, s7, s8, a3, hcall15, hcall16, hcall17, hcall18⟩, ⟨state, 2#u8, s9, s10, s11, a4, hcall21, hcall22, hcall23, hcall24⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair2 : DigestPair D self1.hash := (⟨state1, ⟨state1, 1#u8, s12, s13, s14, a5, hcall27, hcall28, hcall29, hcall30⟩, ⟨state1, 2#u8, s15, s16, s17, a6, hcall32, hcall33, hcall34, hcall35⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair3 : DigestPair D self1.hash := (⟨state2, ⟨state2, 1#u8, s18, s19, s20, a7, hcall38, hcall39, hcall40, hcall41⟩, ⟨state2, 2#u8, s21, s22, s23, a8, hcall43, hcall44, hcall45, hcall46⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair4 : DigestPair D self1.hash := (⟨state3, ⟨state3, 1#u8, s24, s25, s26, a9, hcall49, hcall50, hcall51, hcall52⟩, ⟨state3, 2#u8, s27, s28, s29, a10, hcall54, hcall55, hcall56, hcall57⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair5 : DigestPair D self1.hash := (⟨state4, ⟨state4, 1#u8, s30, s31, s32, a11, hcall60, hcall61, hcall62, hcall63⟩, ⟨state4, 2#u8, s33, s34, s35, a12, hcall65, hcall66, hcall67, hcall68⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair6 : DigestPair D self1.hash := (⟨state5, ⟨state5, 1#u8, s36, s37, s38, a13, hcall71, hcall72, hcall73, hcall74⟩, ⟨state5, 2#u8, s39, s40, s41, a14, hcall76, hcall77, hcall78, hcall79⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pair7 : DigestPair D self1.hash := (⟨state6, ⟨state6, 1#u8, s42, s43, s44, a15, hcall82, hcall83, hcall84, hcall85⟩, ⟨state6, 2#u8, s45, s46, s47, a16, hcall87, hcall88, hcall89, hcall90⟩, rfl, rfl, rfl, rfl⟩ : DigestPair D self1.hash)
  let pairs : List (DigestPair D self1.hash) := [pair0, pair1, pair2, pair3, pair4, pair5, pair6, pair7]
  have hstate0 : state = a2 := by
    have hread := index_mut_readback blocks 0#usize a2 unused index_mut_back (by decide) hcall8
    have hread' : Array.index_usize blocks1 0#usize = ok a2 := by simpa [blocks1] using hread
    exact Result.ok.inj (hcall14.symm.trans hread')
  have hstate1 : state1 = a4 := by
    have hread := update_readback blocks1 1#usize a4 (by decide) blocks4 hcall25
    exact Result.ok.inj (hcall26.symm.trans hread)
  have hstate2 : state2 = a6 := by
    have hread := update_readback blocks4 2#usize a6 (by decide) blocks6 hcall36
    exact Result.ok.inj (hcall37.symm.trans hread)
  have hstate3 : state3 = a8 := by
    have hread := update_readback blocks6 3#usize a8 (by decide) blocks8 hcall47
    exact Result.ok.inj (hcall48.symm.trans hread)
  have hstate4 : state4 = a10 := by
    have hread := update_readback blocks8 4#usize a10 (by decide) blocks10 hcall58
    exact Result.ok.inj (hcall59.symm.trans hread)
  have hstate5 : state5 = a12 := by
    have hread := update_readback blocks10 5#usize a12 (by decide) blocks12 hcall69
    exact Result.ok.inj (hcall70.symm.trans hread)
  have hstate6 : state6 = a14 := by
    have hread := update_readback blocks12 6#usize a14 (by decide) blocks14 hcall80
    exact Result.ok.inj (hcall81.symm.trans hread)
  have hsqueeze0 : Array.index_usize blocks15 0#usize = ok a1 := by
    calc
      Array.index_usize blocks15 0#usize = Array.index_usize blocks13 0#usize :=
        update_readback_other blocks13 7#usize 0#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 0#usize :=
        update_readback_other blocks11 6#usize 0#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = Array.index_usize blocks9 0#usize :=
        update_readback_other blocks9 5#usize 0#usize a11 (by decide) (by decide) (by decide) blocks11 hcall64
      _ = Array.index_usize blocks7 0#usize :=
        update_readback_other blocks7 4#usize 0#usize a9 (by decide) (by decide) (by decide) blocks9 hcall53
      _ = Array.index_usize blocks5 0#usize :=
        update_readback_other blocks5 3#usize 0#usize a7 (by decide) (by decide) (by decide) blocks7 hcall42
      _ = Array.index_usize blocks3 0#usize :=
        update_readback_other blocks3 2#usize 0#usize a5 (by decide) (by decide) (by decide) blocks5 hcall31
      _ = Array.index_usize blocks2 0#usize :=
        update_readback_other blocks2 1#usize 0#usize a3 (by decide) (by decide) (by decide) blocks3 hcall20
      _ = ok a1 := index_mut_readback blocks 0#usize a1 unused index_mut_back (by decide) hcall8
  have hsqueeze1 : Array.index_usize blocks15 1#usize = ok a3 := by
    calc
      Array.index_usize blocks15 1#usize = Array.index_usize blocks13 1#usize := update_readback_other blocks13 7#usize 1#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 1#usize := update_readback_other blocks11 6#usize 1#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = Array.index_usize blocks9 1#usize := update_readback_other blocks9 5#usize 1#usize a11 (by decide) (by decide) (by decide) blocks11 hcall64
      _ = Array.index_usize blocks7 1#usize := update_readback_other blocks7 4#usize 1#usize a9 (by decide) (by decide) (by decide) blocks9 hcall53
      _ = Array.index_usize blocks5 1#usize := update_readback_other blocks5 3#usize 1#usize a7 (by decide) (by decide) (by decide) blocks7 hcall42
      _ = Array.index_usize blocks3 1#usize := update_readback_other blocks3 2#usize 1#usize a5 (by decide) (by decide) (by decide) blocks5 hcall31
      _ = ok a3 := update_readback blocks2 1#usize a3 (by decide) blocks3 hcall20
  have hsqueeze2 : Array.index_usize blocks15 2#usize = ok a5 := by
    calc
      Array.index_usize blocks15 2#usize = Array.index_usize blocks13 2#usize := update_readback_other blocks13 7#usize 2#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 2#usize := update_readback_other blocks11 6#usize 2#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = Array.index_usize blocks9 2#usize := update_readback_other blocks9 5#usize 2#usize a11 (by decide) (by decide) (by decide) blocks11 hcall64
      _ = Array.index_usize blocks7 2#usize := update_readback_other blocks7 4#usize 2#usize a9 (by decide) (by decide) (by decide) blocks9 hcall53
      _ = Array.index_usize blocks5 2#usize := update_readback_other blocks5 3#usize 2#usize a7 (by decide) (by decide) (by decide) blocks7 hcall42
      _ = ok a5 := update_readback blocks3 2#usize a5 (by decide) blocks5 hcall31
  have hsqueeze3 : Array.index_usize blocks15 3#usize = ok a7 := by
    calc
      Array.index_usize blocks15 3#usize = Array.index_usize blocks13 3#usize := update_readback_other blocks13 7#usize 3#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 3#usize := update_readback_other blocks11 6#usize 3#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = Array.index_usize blocks9 3#usize := update_readback_other blocks9 5#usize 3#usize a11 (by decide) (by decide) (by decide) blocks11 hcall64
      _ = Array.index_usize blocks7 3#usize := update_readback_other blocks7 4#usize 3#usize a9 (by decide) (by decide) (by decide) blocks9 hcall53
      _ = ok a7 := update_readback blocks5 3#usize a7 (by decide) blocks7 hcall42
  have hsqueeze4 : Array.index_usize blocks15 4#usize = ok a9 := by
    calc
      Array.index_usize blocks15 4#usize = Array.index_usize blocks13 4#usize := update_readback_other blocks13 7#usize 4#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 4#usize := update_readback_other blocks11 6#usize 4#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = Array.index_usize blocks9 4#usize := update_readback_other blocks9 5#usize 4#usize a11 (by decide) (by decide) (by decide) blocks11 hcall64
      _ = ok a9 := update_readback blocks7 4#usize a9 (by decide) blocks9 hcall53
  have hsqueeze5 : Array.index_usize blocks15 5#usize = ok a11 := by
    calc
      Array.index_usize blocks15 5#usize = Array.index_usize blocks13 5#usize := update_readback_other blocks13 7#usize 5#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = Array.index_usize blocks11 5#usize := update_readback_other blocks11 6#usize 5#usize a13 (by decide) (by decide) (by decide) blocks13 hcall75
      _ = ok a11 := update_readback blocks9 5#usize a11 (by decide) blocks11 hcall64
  have hsqueeze6 : Array.index_usize blocks15 6#usize = ok a13 := by
    calc
      Array.index_usize blocks15 6#usize = Array.index_usize blocks13 6#usize := update_readback_other blocks13 7#usize 6#usize a15 (by decide) (by decide) (by decide) blocks15 hcall86
      _ = ok a13 := update_readback blocks11 6#usize a13 (by decide) blocks13 hcall75
  have hsqueeze7 : Array.index_usize blocks15 7#usize = ok a15 :=
    update_readback blocks13 7#usize a15 (by decide) blocks15 hcall86
  have hadvance0 : Array.index_usize blocks16 0#usize = ok a2 := by
    calc
      Array.index_usize blocks16 0#usize = Array.index_usize blocks14 0#usize := update_readback_other blocks14 7#usize 0#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 0#usize := update_readback_other blocks12 6#usize 0#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = Array.index_usize blocks10 0#usize := update_readback_other blocks10 5#usize 0#usize a12 (by decide) (by decide) (by decide) blocks12 hcall69
      _ = Array.index_usize blocks8 0#usize := update_readback_other blocks8 4#usize 0#usize a10 (by decide) (by decide) (by decide) blocks10 hcall58
      _ = Array.index_usize blocks6 0#usize := update_readback_other blocks6 3#usize 0#usize a8 (by decide) (by decide) (by decide) blocks8 hcall47
      _ = Array.index_usize blocks4 0#usize := update_readback_other blocks4 2#usize 0#usize a6 (by decide) (by decide) (by decide) blocks6 hcall36
      _ = Array.index_usize blocks1 0#usize := update_readback_other blocks1 1#usize 0#usize a4 (by decide) (by decide) (by decide) blocks4 hcall25
      _ = ok a2 := index_mut_readback blocks 0#usize a2 unused index_mut_back (by decide) hcall8
  have hadvance1 : Array.index_usize blocks16 1#usize = ok a4 := by
    calc
      Array.index_usize blocks16 1#usize = Array.index_usize blocks14 1#usize := update_readback_other blocks14 7#usize 1#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 1#usize := update_readback_other blocks12 6#usize 1#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = Array.index_usize blocks10 1#usize := update_readback_other blocks10 5#usize 1#usize a12 (by decide) (by decide) (by decide) blocks12 hcall69
      _ = Array.index_usize blocks8 1#usize := update_readback_other blocks8 4#usize 1#usize a10 (by decide) (by decide) (by decide) blocks10 hcall58
      _ = Array.index_usize blocks6 1#usize := update_readback_other blocks6 3#usize 1#usize a8 (by decide) (by decide) (by decide) blocks8 hcall47
      _ = Array.index_usize blocks4 1#usize := update_readback_other blocks4 2#usize 1#usize a6 (by decide) (by decide) (by decide) blocks6 hcall36
      _ = ok a4 := update_readback blocks1 1#usize a4 (by decide) blocks4 hcall25
  have hadvance2 : Array.index_usize blocks16 2#usize = ok a6 := by
    calc
      Array.index_usize blocks16 2#usize = Array.index_usize blocks14 2#usize := update_readback_other blocks14 7#usize 2#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 2#usize := update_readback_other blocks12 6#usize 2#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = Array.index_usize blocks10 2#usize := update_readback_other blocks10 5#usize 2#usize a12 (by decide) (by decide) (by decide) blocks12 hcall69
      _ = Array.index_usize blocks8 2#usize := update_readback_other blocks8 4#usize 2#usize a10 (by decide) (by decide) (by decide) blocks10 hcall58
      _ = Array.index_usize blocks6 2#usize := update_readback_other blocks6 3#usize 2#usize a8 (by decide) (by decide) (by decide) blocks8 hcall47
      _ = ok a6 := update_readback blocks4 2#usize a6 (by decide) blocks6 hcall36
  have hadvance3 : Array.index_usize blocks16 3#usize = ok a8 := by
    calc
      Array.index_usize blocks16 3#usize = Array.index_usize blocks14 3#usize := update_readback_other blocks14 7#usize 3#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 3#usize := update_readback_other blocks12 6#usize 3#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = Array.index_usize blocks10 3#usize := update_readback_other blocks10 5#usize 3#usize a12 (by decide) (by decide) (by decide) blocks12 hcall69
      _ = Array.index_usize blocks8 3#usize := update_readback_other blocks8 4#usize 3#usize a10 (by decide) (by decide) (by decide) blocks10 hcall58
      _ = ok a8 := update_readback blocks6 3#usize a8 (by decide) blocks8 hcall47
  have hadvance4 : Array.index_usize blocks16 4#usize = ok a10 := by
    calc
      Array.index_usize blocks16 4#usize = Array.index_usize blocks14 4#usize := update_readback_other blocks14 7#usize 4#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 4#usize := update_readback_other blocks12 6#usize 4#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = Array.index_usize blocks10 4#usize := update_readback_other blocks10 5#usize 4#usize a12 (by decide) (by decide) (by decide) blocks12 hcall69
      _ = ok a10 := update_readback blocks8 4#usize a10 (by decide) blocks10 hcall58
  have hadvance5 : Array.index_usize blocks16 5#usize = ok a12 := by
    calc
      Array.index_usize blocks16 5#usize = Array.index_usize blocks14 5#usize := update_readback_other blocks14 7#usize 5#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = Array.index_usize blocks12 5#usize := update_readback_other blocks12 6#usize 5#usize a14 (by decide) (by decide) (by decide) blocks14 hcall80
      _ = ok a12 := update_readback blocks10 5#usize a12 (by decide) blocks12 hcall69
  have hadvance6 : Array.index_usize blocks16 6#usize = ok a14 := by
    calc
      Array.index_usize blocks16 6#usize = Array.index_usize blocks14 6#usize := update_readback_other blocks14 7#usize 6#usize a16 (by decide) (by decide) (by decide) blocks16 hcall91
      _ = ok a14 := update_readback blocks12 6#usize a14 (by decide) blocks14 hcall80
  have hadvance7 : Array.index_usize blocks16 7#usize = ok a16 :=
    update_readback blocks14 7#usize a16 (by decide) blocks16 hcall91
  have hmaterial : materializedOutputs pairs blocks15 blocks16 := by
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · subst i
      refine ⟨pair0, by simp [pairs], ?_, ?_⟩
      · rw [index8_zero hi]
        simpa only [pair0] using hsqueeze0
      · rw [index8_zero hi]
        simpa only [pair0] using hadvance0
    · subst i
      refine ⟨pair1, by simp [pairs], ?_, ?_⟩
      · rw [index8_one hi]
        simpa only [pair1] using hsqueeze1
      · rw [index8_one hi]
        simpa only [pair1] using hadvance1
    · subst i
      refine ⟨pair2, by simp [pairs], ?_, ?_⟩
      · rw [index8_two hi]
        simpa only [pair2] using hsqueeze2
      · rw [index8_two hi]
        simpa only [pair2] using hadvance2
    · subst i
      refine ⟨pair3, by simp [pairs], ?_, ?_⟩
      · rw [index8_three hi]
        simpa only [pair3] using hsqueeze3
      · rw [index8_three hi]
        simpa only [pair3] using hadvance3
    · subst i
      refine ⟨pair4, by simp [pairs], ?_, ?_⟩
      · rw [index8_four hi]
        simpa only [pair4] using hsqueeze4
      · rw [index8_four hi]
        simpa only [pair4] using hadvance4
    · subst i
      refine ⟨pair5, by simp [pairs], ?_, ?_⟩
      · rw [index8_five hi]
        simpa only [pair5] using hsqueeze5
      · rw [index8_five hi]
        simpa only [pair5] using hadvance5
    · subst i
      refine ⟨pair6, by simp [pairs], ?_, ?_⟩
      · rw [index8_six hi]
        simpa only [pair6] using hsqueeze6
      · rw [index8_six hi]
        simpa only [pair6] using hadvance6
    · subst i
      refine ⟨pair7, by simp [pairs], ?_, ?_⟩
      · rw [index8_seven hi]
        simpa only [pair7] using hsqueeze7
      · rw [index8_seven hi]
        simpa only [pair7] using hadvance7
  refine ⟨pairs, hcall1, hdecode, ha, rfl, ?_, ?_, hmaterial⟩
  · exact ⟨pair0, [pair1, pair2, pair3, pair4, pair5, pair6, pair7], rfl, rfl⟩
  · simp [stateChain, pairs, pair0, pair1, pair2, pair3, pair4, pair5, pair6, pair7,
      hstate0, hstate1, hstate2, hstate3, hstate4, hstate5, hstate6]

/-- Compatibility projection retaining the original successful-call API. -/
theorem queries_success_with_digest_pairs {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧ pairs.length = 8 := by
  obtain ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter,
      hlen, _hfirst, _hchain, _hmaterial⟩ :=
    queries_success_with_digest_pairs_full B D self after row payload out h
  exact ⟨absorbed, blocks, advances, selected, pairs, habs, hdecode, hafter, hlen⟩

#print axioms stateChain
#print axioms materializedOutputs
#print axioms queries_success_with_digest_pairs_full
#print axioms queries_success_with_digest_pairs
end AspisR1PublicPreparation.Query31SourceSchedule
end
