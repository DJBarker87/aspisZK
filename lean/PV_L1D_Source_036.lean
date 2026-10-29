import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_036
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (masks : Array Std.U16 64#usize) (column : Std.Usize)
  (mask_only_columns_inactive_balanced : Std.Usize) :
  Logged (ControlFlow (Std.Usize × Std.Usize) Std.Usize)
  := do
  let _ ← observe .balanceAudit 0 (ok ())
  if column < 10#usize
  then
    let v ← PV_L1D_Logged.lift (Array.index_usize mask_only column)
    let s := alloc.vec.Vec.deref v
    let m ← PV_L1D_Logged.lift (prover.inactive_sum_m31 s masks)
    let m1 ← PV_L1D_Logged.lift (aspis_core.field.M31.ZERO)
    let b ← PV_L1D_Logged.lift (aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq m m1)
    let mask_only_columns_inactive_balanced1 ← PV_L1D_Logged.lift (if b
      then
        Pure.pure (Std.Usize.wrapping_add mask_only_columns_inactive_balanced 1#usize)
      else Pure.pure mask_only_columns_inactive_balanced)
    let column1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add column 1#usize))
    Pure.pure (cont (column1, mask_only_columns_inactive_balanced1))
  else Pure.pure (done mask_only_columns_inactive_balanced)

theorem complete_result
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (masks : Array Std.U16 64#usize) (column : Std.Usize)
  (mask_only_columns_inactive_balanced : Std.Usize) :
  erase (produce mask_only masks column mask_only_columns_inactive_balanced) = prover.audit_masks_loop1.body mask_only masks column mask_only_columns_inactive_balanced := by
  unfold produce
  conv_rhs => unfold prover.audit_masks_loop1.body
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_036
