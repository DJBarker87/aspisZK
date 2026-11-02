import PV_EVH_Runtime
set_option autoImplicit false
namespace PV_EVH_RuntimeValueBind
open Aeneas Aeneas.Std PV_EVH_Runtime
/-- Capacity/runtime effects precede the source value continuation. Faults
retain their world/prefix and do not acquire a source-value projection. -/
theorem value_bind_fixed {A B : Type} (m : Q A) (a : A)
    (k : A → Q B) (r : Result B)
    (hm : PartialView m (.ok a)) (hk : PartialView (k a) r) :
    PartialView (PV_EVH_Runtime.bind m k) r := by
  intro w s hs
  cases he : (m w).outcome with
  | fault e => simp only [PV_EVH_Runtime.bind,he,sourceProjection] at hs; cases hs
  | exhausted => simp only [PV_EVH_Runtime.bind,he,sourceProjection] at hs; cases hs
  | returned t =>
    have ht := hm w t (by rw [he]; rfl)
    have he' : (m w).outcome = .returned (.ok a) := he.trans (congrArg _ ht.symm)
    simp only [PV_EVH_Runtime.bind,he'] at hs
    exact hk (m w).state s hs
#print axioms value_bind_fixed
end PV_EVH_RuntimeValueBind
