import PV_EVH_Prefix
set_option autoImplicit false
namespace PV_EVH_LiftLaws
open Aeneas Aeneas.Std PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
/-- This is an equality for already interpreted primitive computations;
it does not authorize lifting an effectful source helper. -/
theorem bind_lift {A B : Type} (r : Result A) (f : A → Result B) :
    PV_EVH_Prefix.bind (PV_EVH_Prefix.lift r) (fun a => PV_EVH_Prefix.lift (f a)) =
      PV_EVH_Prefix.lift (Aeneas.Std.bind r f) := by
  funext w
  cases r <;> rfl
#print axioms bind_lift
-- Inspect actual loaded checked-index definitions for the nonzero-loop audit.
#print Aeneas.Std.Array.index_usize
#check Aeneas.Std.Array.index_usize_spec
#print Aeneas.Std.Usize.wrapping_add
end PV_EVH_LiftLaws
