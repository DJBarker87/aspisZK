import PV_EVH_Prefix
set_option autoImplicit false
namespace PV_EVH_SliceBind
open Aeneas Aeneas.Std PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
/-- Normalize only a pure language-level bind; this makes no claim about an
allocator, runtime helper or effectful external. -/
theorem pure_bind_fixed {A B : Type} (a : A) (k : A → P B) (r : Result B)
    (h : FinishedView (k a) r) :
    FinishedView (PV_EVH_Prefix.bind (PV_EVH_Prefix.lift (.ok a)) k) r := by
  intro w s hs
  exact h w s hs
#print axioms pure_bind_fixed
end PV_EVH_SliceBind
