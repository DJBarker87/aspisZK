import NKI_InitialTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialTraceFactor
open Aeneas Aeneas.Std Result FIq_Native
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
theorem source (p : Public) (o : Openings) (s : Selectors) :
 (do let l←NKI_InitialTrace.run p o s;ok (NKI_InitialInvocation.output l))=NKI_InitialPrefix.run p o s := by
 simp only [NKI_InitialTrace.run,NKI_InitialPrefix.run,NKI_InitialInvocation.output,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
 congr 1
/-- SAME trace output supplies all primitive/std Result equations. -/
theorem clauses (public1 : Public) (openings : Openings) (selectors : Selectors) (l : Locals)
 (run : NKI_InitialTrace.run public1 openings selectors=ok l) :
 NKI_InitialInvocation.Clauses public1 openings selectors l := by
 unfold NKI_InitialTrace.run at run
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
 have eq:=Result.ok.inj run
 cases eq
 exact ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,c57⟩
#print axioms source
#print axioms clauses
end AspisR1.NKI_InitialTraceFactor
end
