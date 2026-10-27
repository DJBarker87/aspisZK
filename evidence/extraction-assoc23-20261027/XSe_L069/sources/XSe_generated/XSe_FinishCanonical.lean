import XSe_PowerDomain
import XRz_FinishMaterialize
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_FinishCanonical
/-- Arbitrary raw rows materialize canonical fields, independent of phase. -/
theorem row (r : S8OwnedP6Finish.Row) :
 XRp_PowersQAdd.CanonicalQ (XRz_FinishValue.newQ (S8OwnedP6Finish.modelValue r)) := by
 have h0 := (S8OwnedP6Finish.modelValue_coordinates r 0).2
 have h1 := (S8OwnedP6Finish.modelValue_coordinates r 1).2
 have h2 := (S8OwnedP6Finish.modelValue_coordinates r 2).2
 have h3 := (S8OwnedP6Finish.modelValue_coordinates r 3).2
 exact ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
/-- Full materialization success and canonicality at every destination cell. -/
theorem source (b : verifier.BatchedWeights) (s : Slice aspis_core.field.QM31)
 (lengths : s.length≤b.raw.length) :
 ∃ out : Slice aspis_core.field.QM31, verifier.BatchedWeights.finish b s=ok out ∧
 out.length=s.length ∧ ∀ j, (h : j<out.val.length) → XRp_PowersQAdd.CanonicalQ (out.val[j]'h) := by
 obtain ⟨out,run,len,cells⟩ := XRz_FinishMaterialize.source b s lengths
 refine ⟨out,run,len,?_⟩
 intro j hj
 have same := cells j (by rw [←len];exact hj)
 rw [List.getElem?_eq_getElem hj] at same
 have value := Option.some.inj same
 rw [value,XRz_FinishMaterialize.rowValue,dif_pos (by rw [len] at hj;omega)]
 exact row _
#print axioms row
#print axioms source
end XSe_FinishCanonical
