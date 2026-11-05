import NHI_PowersReuse
set_option autoImplicit false
namespace NHI_FactoredProducers
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev one := FIo_Native.aspis_core.field.QM31.ONE

theorem one_canonical : canonQ one := by
 unfold one FIo_Native.aspis_core.field.QM31.ONE
 simp only [canonQ,canonC,LPi_CMProduct.Canon]
 decide

theorem square (x : NQ) (hx : canonQ x) :
 ∃ out,FIo_Native.aspis_core.field.QM31.square x=ok out ∧ canonQ out := by
 obtain ⟨out,run,co,value⟩ := NGH_QSquareRef.cohort x hx
 exact ⟨out,(NGH_QSquareRef.model_eq x).symm.trans run,co⟩

/-- Source-ordered q/q4/q8/q12/q16 producers, including the frozen unused q^4
call. Square is the inherited CLOSED packet; no multiplication is run in Kani. -/
def run (q : NQ) : Result (Array NQ 4#usize × Array NQ 4#usize × NQ × NQ) := do
 let q1 ← FIo_Native.aspis_core.field.QM31.mul one q
 let q2 ← FIo_Native.aspis_core.field.QM31.mul q1 q
 let q3 ← FIo_Native.aspis_core.field.QM31.mul q2 q
 let _ ← FIo_Native.aspis_core.field.QM31.mul q3 q
 let q4 ← FIo_Native.aspis_core.field.QM31.square q2
 let q8 ← FIo_Native.aspis_core.field.QM31.square q4
 let q12 ← FIo_Native.aspis_core.field.QM31.mul q8 q4
 let q16 ← FIo_Native.aspis_core.field.QM31.square q8
 ok (Array.make 4#usize [one,q1,q2,q3],Array.make 4#usize [one,q4,q8,q12],q4,q16)

theorem total (q : NQ) (hq : canonQ q) :
 ∃ low high q4 q16,run q=ok (low,high,q4,q16) ∧
 (∀ x∈low.val,canonQ x) ∧ (∀ x∈high.val,canonQ x) ∧ canonQ q4 ∧ canonQ q16 := by
 obtain ⟨q1,h1,c1,_⟩ := LPi_TowerValues.qm_mul one q one_canonical hq
 obtain ⟨q2,h2,c2,_⟩ := LPi_TowerValues.qm_mul q1 q c1 hq
 obtain ⟨q3,h3,c3,_⟩ := LPi_TowerValues.qm_mul q2 q c2 hq
 obtain ⟨unused,hu,cu,_⟩ := LPi_TowerValues.qm_mul q3 q c3 hq
 obtain ⟨q4,h4,c4⟩ := square q2 c2
 obtain ⟨q8,h8,c8⟩ := square q4 c4
 obtain ⟨q12,h12,c12,_⟩ := LPi_TowerValues.qm_mul q8 q4 c8 c4
 obtain ⟨q16,h16,c16⟩ := square q8 c8
 refine ⟨Array.make 4#usize [one,q1,q2,q3],Array.make 4#usize [one,q4,q8,q12],q4,q16,?_,?_,?_,c4,c16⟩
 · simp only [run,h1,h2,h3,hu,h4,h8,h12,h16,bind_tc_ok]
 · intro x hx
   simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl|rfl|rfl
   · exact one_canonical
   · exact c1
   · exact c2
   · exact c3
 · intro x hx
   simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl|rfl|rfl
   · exact one_canonical
   · exact c4
   · exact c8
   · exact c12

#print axioms one_canonical
#print axioms square
#print axioms total
end NHI_FactoredProducers
