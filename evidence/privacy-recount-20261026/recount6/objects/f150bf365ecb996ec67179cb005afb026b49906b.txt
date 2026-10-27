import PV_B1_PoleBody
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleBridge
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258 PV_B1_PoleBody

theorem body (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (clear : Bool) (row : Usize) :
    all_slots_clear_loop0.body values masks chi clear row =
      PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row :=
  (PV_B1_PoleBody.source values masks chi clear row).trans
    (PV_B1_PoleBody.original values masks chi clear row).symm

theorem loop_result (values : Rows) (masks : Array U16 64#usize) (chi : Q)
    (clear : Bool) (row : Usize) :
    all_slots_clear_loop0 values masks chi clear row =
      PV_B1_PoleOriginal.reference.all_slots_clear_loop values masks chi clear row := by
  unfold all_slots_clear_loop0 PV_B1_PoleOriginal.reference.all_slots_clear_loop
  apply congrArg (fun f : Bool × Usize → Result (ControlFlow (Bool × Usize) Bool) =>
    loop f (clear,row))
  funext state
  rcases state with ⟨c,r⟩
  exact body values masks chi c r

theorem op258_source (values : Rows) (masks : Array U16 64#usize) (chi : Q) :
    all_slots_clear values masks chi = PV_B1_PoleOriginal.reference.all_slots_clear values masks chi :=
  loop_result values masks chi true 0#usize
#print axioms body
#print axioms loop_result
#print axioms op258_source
end PV_B1_PoleBridge
