import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_036
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
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
    let v ← Array.index_usize mask_only column
    let s := alloc.vec.Vec.deref v
    let m ← prover.inactive_sum_m31 s masks
    let m1 ← aspis_core.field.M31.ZERO
    let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq m m1
    let mask_only_columns_inactive_balanced1 ←
      if b
      then
        ok (Std.Usize.wrapping_add mask_only_columns_inactive_balanced 1#usize)
      else ok mask_only_columns_inactive_balanced
    let column1 ← Aeneas.Std.lift (Std.Usize.wrapping_add column 1#usize)
    ok (cont (column1, mask_only_columns_inactive_balanced1))
  else ok (done mask_only_columns_inactive_balanced)

theorem complete_result
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (masks : Array Std.U16 64#usize) (column : Std.Usize)
  (mask_only_columns_inactive_balanced : Std.Usize) : :
  erase (produce mask_only masks column mask_only_columns_inactive_balanced) = prover.audit_masks_loop1.body mask_only masks column mask_only_columns_inactive_balanced := by
  unfold produce prover.audit_masks_loop1.body
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_036
