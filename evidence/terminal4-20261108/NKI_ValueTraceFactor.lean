import NKI_ValueTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueTraceFactor
open Aeneas Aeneas.Std Result FIq_Native
open NKI_ValuePrefix (Openings Selectors)
open NKI_ValueTrace (Locals)
theorem source (o : Openings) (s : Selectors) :
 (do let l←NKI_ValueTrace.run o s;ok (NKI_ValueTrace.output l))=NKI_ValuePrefix.run o s := by
 simp only [NKI_ValueTrace.run,NKI_ValuePrefix.run,NKI_ValueTrace.output,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
 congr 1
theorem clauses (openings : Openings) (selectors : Selectors) (l : Locals)
 (run : NKI_ValueTrace.run openings selectors=ok l) : NKI_ValueTrace.Clauses openings selectors l := by
 unfold NKI_ValueTrace.run at run
 obtain ⟨value_selectors,c0,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q,c1,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q1,c2,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q2,c3,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q3,c4,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q4,c5,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨range_selector,c6,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨⟨openings1, range1⟩,c7,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨⟨openings2, range2⟩,c8,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨⟨openings3, range3⟩,c9,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q5,c10,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q6,c11,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨i,c12,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q7,c13,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q8,c14,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q9,c15,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨i1,c16,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q10,c17,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨reconstructed,c18,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q11,c19,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q12,c20,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨range4,c21,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q13,c22,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨range5,c23,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨q14,c24,run⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨range6,c25,run⟩ := FIv_Map.bind_success _ _ _ run
 have same:=Result.ok.inj run
 cases same
 exact ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25⟩
#print axioms source
#print axioms clauses
end AspisR1.NKI_ValueTraceFactor
end
