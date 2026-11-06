import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialInvocation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors Tail)
structure Locals where
 s : Slice (core.ops.range.Range Usize)
 nodes : NQ
 q : NQ
 q1 : NQ
 q2 : NQ
 q3 : NQ
 q4 : NQ
 q5 : NQ
 first_common : NQ
 q6 : NQ
 q7 : NQ
 q8 : NQ
 transfer_first : NQ
 fixed : NQ
 private_chunk_eight : NQ
 private_chunk_two : NQ
 q9 : NQ
 q10 : NQ
 q11 : NQ
 full_initial_selector : NQ
 rate_initial_selector : NQ
 full : FIv_PreparedNew.NP
 q12 : NQ
 full_or_rate : FIv_PreparedNew.NP
 initial : Array NQ 16#usize
 q13 : NQ
 note_first : NQ
 q14 : NQ
 q15 : NQ
 q16 : NQ
 q17 : NQ
 domain : NQ
 q18 : NQ
 q19 : NQ
 q20 : NQ
 q21 : NQ
 length : NQ
 q22 : NQ
 q23 : NQ
 q24 : NQ
 initial1 : Array NQ 16#usize
 i : Usize
 q25 : NQ
 q26 : NQ
 q27 : NQ
 initial2 : Array NQ 16#usize
 q28 : NQ
 q29 : NQ
 q30 : NQ
 q31 : NQ
 q32 : NQ
 q33 : NQ
 q34 : NQ
 q35 : NQ
 chunk_eight : NQ
 q36 : NQ
 q37 : NQ
 chunk_two : NQ
 chunk_eight1 : NQ
 chunk_two1 : NQ
 q38 : NQ
def Clauses (public1 : Public) (openings : Openings) (selectors : Selectors) (l : Locals) : Prop :=
 let s:=l.s
 let nodes:=l.nodes
 let q:=l.q
 let q1:=l.q1
 let q2:=l.q2
 let q3:=l.q3
 let q4:=l.q4
 let q5:=l.q5
 let first_common:=l.first_common
 let q6:=l.q6
 let q7:=l.q7
 let q8:=l.q8
 let transfer_first:=l.transfer_first
 let fixed:=l.fixed
 let private_chunk_eight:=l.private_chunk_eight
 let private_chunk_two:=l.private_chunk_two
 let q9:=l.q9
 let q10:=l.q10
 let q11:=l.q11
 let full_initial_selector:=l.full_initial_selector
 let rate_initial_selector:=l.rate_initial_selector
 let full:=l.full
 let q12:=l.q12
 let full_or_rate:=l.full_or_rate
 let initial:=l.initial
 let q13:=l.q13
 let note_first:=l.note_first
 let q14:=l.q14
 let q15:=l.q15
 let q16:=l.q16
 let q17:=l.q17
 let domain:=l.domain
 let q18:=l.q18
 let q19:=l.q19
 let q20:=l.q20
 let q21:=l.q21
 let length:=l.length
 let q22:=l.q22
 let q23:=l.q23
 let q24:=l.q24
 let initial1:=l.initial1
 let i:=l.i
 let q25:=l.q25
 let q26:=l.q26
 let q27:=l.q27
 let initial2:=l.initial2
 let q28:=l.q28
 let q29:=l.q29
 let q30:=l.q30
 let q31:=l.q31
 let q32:=l.q32
 let q33:=l.q33
 let q34:=l.q34
 let q35:=l.q35
 let chunk_eight:=l.chunk_eight
 let q36:=l.q36
 let q37:=l.q37
 let chunk_two:=l.chunk_two
 let chunk_eight1:=l.chunk_eight1
 let chunk_two1:=l.chunk_two1
 let q38:=l.q38
 (lift (Array.to_slice
      (Array.make 2#usize [
        ({ start := 4#usize, «end» := 25#usize } : core.ops.range.Range
        Std.Usize), ({ start := 33#usize, «end» := 57#usize } :
        core.ops.range.Range Std.Usize)
        ]))=ok s) ∧
 (pool_v1.pair_forest_semantic_terminal.sum_high selectors s=ok nodes) ∧
 (Array.index_usize selectors.high 0#usize=ok q) ∧
 (Array.index_usize selectors.high 1#usize=ok q1) ∧
 (field.QM31.add q q1=ok q2) ∧
 (Array.index_usize selectors.high 25#usize=ok q3) ∧
 (field.QM31.add q2 q3=ok q4) ∧
 (Array.index_usize selectors.high 30#usize=ok q5) ∧
 (field.QM31.add q4 q5=ok first_common) ∧
 (Array.index_usize selectors.high 27#usize=ok q6) ∧
 (Array.index_usize selectors.high 28#usize=ok q7) ∧
 (Array.index_usize selectors.high 29#usize=ok q8) ∧
 (pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
      public1.variant q6 q7 q8=ok (transfer_first, fixed, private_chunk_eight, private_chunk_two)) ∧
 (Array.index_usize selectors.low 0#usize=ok q9) ∧
 (field.QM31.add first_common transfer_first=ok q10) ∧
 (field.QM31.add q10 fixed=ok q11) ∧
 (field.QM31.mul q9 q11=ok full_initial_selector) ∧
 (field.QM31.mul q9 nodes=ok rate_initial_selector) ∧
 (field.PreparedQm31Multiplier.new full_initial_selector=ok full) ∧
 (field.QM31.add full_initial_selector rate_initial_selector=ok q12) ∧
 (field.PreparedQm31Multiplier.new q12=ok full_or_rate) ∧
 (array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO (full_or_rate, openings, full)=ok initial) ∧
 (field.QM31.add q1 q5=ok q13) ∧
 (field.QM31.add q13 transfer_first=ok note_first) ∧
 (field.QM31.mul_m31 q spend.DOMAIN_OWNER_KEY=ok q14) ∧
 (field.QM31.mul_m31 note_first spend.DOMAIN_NOTE=ok q15) ∧
 (field.QM31.add q14 q15=ok q16) ∧
 (field.QM31.mul_m31 q3 spend.DOMAIN_NULLIFIER=ok q17) ∧
 (field.QM31.add q16 q17=ok domain) ∧
 (field.QM31.mul_m31 q 8#u32=ok q18) ∧
 (field.QM31.mul_m31 note_first 18#u32=ok q19) ∧
 (field.QM31.add q18 q19=ok q20) ∧
 (field.QM31.mul_m31 q3 16#u32=ok q21) ∧
 (field.QM31.add q20 q21=ok length) ∧
 (Array.index_usize initial poseidon2.RATE=ok q22) ∧
 (field.QM31.mul q9 domain=ok q23) ∧
 (field.QM31.sub q22 q23=ok q24) ∧
 (Array.update initial poseidon2.RATE q24=ok initial1) ∧
 (poseidon2.RATE + 1#usize=ok i) ∧
 (Array.index_usize initial1 i=ok q25) ∧
 (field.QM31.mul q9 length=ok q26) ∧
 (field.QM31.sub q25 q26=ok q27) ∧
 (Array.update initial1 i q27=ok initial2) ∧
 (field.QM31.add q q1=ok q28) ∧
 (Array.index_usize selectors.high 2#usize=ok q29) ∧
 (field.QM31.add q28 q29=ok q30) ∧
 (field.QM31.add q30 q3=ok q31) ∧
 (Array.index_usize selectors.high 26#usize=ok q32) ∧
 (field.QM31.add q31 q32=ok q33) ∧
 (field.QM31.add q33 q5=ok q34) ∧
 (Array.index_usize selectors.high 31#usize=ok q35) ∧
 (field.QM31.add q34 q35=ok chunk_eight) ∧
 (Array.index_usize selectors.high 3#usize=ok q36) ∧
 (Array.index_usize selectors.high 32#usize=ok q37) ∧
 (field.QM31.add q36 q37=ok chunk_two) ∧
 (field.QM31.add chunk_eight private_chunk_eight=ok chunk_eight1) ∧
 (field.QM31.add chunk_two private_chunk_two=ok chunk_two1) ∧
 (Array.index_usize selectors.low 12#usize=ok q38)
def output (l : Locals) : Tail := ⟨l.initial2,l.q38,l.fixed,l.chunk_two1,l.chunk_eight1,l.nodes⟩
/-- Every complete child Result and std operation at its SAME decoded source
arguments is an OUTPUT of the concrete prefix. No independently chosen run. -/
theorem source (public1 : Public) (openings : Openings) (selectors : Selectors) (t : Tail)
 (run : NKI_InitialPrefix.run public1 openings selectors=ok t) :
 ∃ l,Clauses public1 openings selectors l ∧ output l=t := by
 unfold NKI_InitialPrefix.run at run
 obtain ⟨s,c0,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨nodes,c1,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q,c2,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q1,c3,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q2,c4,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q3,c5,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q4,c6,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q5,c7,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨first_common,c8,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q6,c9,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q7,c10,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q8,c11,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨⟨transfer_first, fixed, private_chunk_eight, private_chunk_two⟩,c12,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q9,c13,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q10,c14,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q11,c15,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨full_initial_selector,c16,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨rate_initial_selector,c17,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨full,c18,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q12,c19,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨full_or_rate,c20,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨initial,c21,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q13,c22,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨note_first,c23,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q14,c24,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q15,c25,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q16,c26,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q17,c27,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨domain,c28,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q18,c29,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q19,c30,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q20,c31,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q21,c32,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨length,c33,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q22,c34,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q23,c35,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q24,c36,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨initial1,c37,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨i,c38,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q25,c39,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q26,c40,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q27,c41,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨initial2,c42,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q28,c43,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q29,c44,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q30,c45,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q31,c46,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q32,c47,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q33,c48,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q34,c49,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q35,c50,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨chunk_eight,c51,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q36,c52,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q37,c53,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨chunk_two,c54,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨chunk_eight1,c55,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨chunk_two1,c56,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q38,c57,run⟩ := FIv_Map.bind_success _ _ _ run
 let l : Locals := ⟨s,nodes,q,q1,q2,q3,q4,q5,first_common,q6,q7,q8,transfer_first,fixed,private_chunk_eight,private_chunk_two,q9,q10,q11,full_initial_selector,rate_initial_selector,full,q12,full_or_rate,initial,q13,note_first,q14,q15,q16,q17,domain,q18,q19,q20,q21,length,q22,q23,q24,initial1,i,q25,q26,q27,initial2,q28,q29,q30,q31,q32,q33,q34,q35,chunk_eight,q36,q37,chunk_two,chunk_eight1,chunk_two1,q38⟩
 exact ⟨l,⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,c57⟩,Result.ok.inj run⟩
#print axioms source
end AspisR1.NKI_InitialInvocation
end
