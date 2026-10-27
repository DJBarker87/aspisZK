import F3K_ArrayFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
namespace AspisR1.F3K_QueryChain
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
/-- Every successful installed query executes the complete eight-pair chain,
including the suffix not chosen by the decoder. -/
theorem chain {H : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed calls,
      transcript.Transcript.absorb D self row payload = ok absorbed ∧
      F3J_QueryPairs.Pairs D absorbed.hash 8 absorbed.state calls := by
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
  have state7_eq : state7 = a16 := Result.ok.inj
    (hcall92.symm.trans (F3K_ArrayFacts.updated _ _ 7#usize a16 hcall91))
  cases state7_eq
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
  refine ⟨self1,_,hcall1,?_⟩
  refine F3J_QueryPairs.Pairs.cons hcall7 hcall12 ?_
  refine F3J_QueryPairs.Pairs.cons hcall18 hcall24 ?_
  refine F3J_QueryPairs.Pairs.cons hcall29 hcall35 ?_
  refine F3J_QueryPairs.Pairs.cons hcall40 hcall46 ?_
  refine F3J_QueryPairs.Pairs.cons hcall51 hcall57 ?_
  refine F3J_QueryPairs.Pairs.cons hcall62 hcall68 ?_
  refine F3J_QueryPairs.Pairs.cons hcall73 hcall79 ?_
  refine F3J_QueryPairs.Pairs.cons hcall84 hcall90 ?_
  exact .nil _

#print axioms chain
end AspisR1.F3K_QueryChain
