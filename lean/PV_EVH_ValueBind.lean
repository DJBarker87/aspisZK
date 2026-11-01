import PV_EVH_Prefix
set_option autoImplicit false
namespace PV_EVH_ValueBind
open Aeneas Aeneas.Std PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
/-- A source value may have runtime effects. Erasure requires its explicit
compatibility premise; no allocator success or native adequacy follows. -/
theorem value_bind_fixed {A B : Type} (m : P A) (a : A)
    (k : A → P B) (r : Result B)
    (hm : FinishedView m (.ok a)) (hk : FinishedView (k a) r) :
    FinishedView (PV_EVH_Prefix.bind m k) r := by
  intro w s hs
  cases he : (m w).status with
  | exhausted =>
    simp only [PV_EVH_Prefix.bind,he] at hs
    cases hs
  | finished t =>
    have ht := hm w t he
    have he' : (m w).status = .finished (.ok a) :=
      he.trans (congrArg _ ht.symm)
    simp only [PV_EVH_Prefix.bind,he'] at hs
    exact hk (m w).world s hs
#print axioms value_bind_fixed
end PV_EVH_ValueBind
