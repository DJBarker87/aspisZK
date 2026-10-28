import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_AuditMasksBody0
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (masks : Array Std.U16 64#usize) (c1_columns_inactive_balanced : Std.Usize)
  (column : Std.Usize) :
  P (ControlFlow (Std.Usize × Std.Usize) Std.Usize) := do
  let i := Slice.len c1
  if column < i then
    let v ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize c1 column)
    let s := alloc.vec.Vec.deref v
    let m ← invoke "prover.inactive_sum_m31" (fun ops =>
        letI : ExternalFuns := ops
        prover.inactive_sum_m31 s masks)
    let m1 ← invoke "aspis_core.field.M31.ZERO" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.M31.ZERO)
    let b ← invoke "aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq m m1)
    PV_W_StructuredBinds.join (do
      if b then
        pure (Std.Usize.wrapping_add c1_columns_inactive_balanced 1#usize)
      else
        pure c1_columns_inactive_balanced) (fun c1_columns_inactive_balanced1 => do
      let column1 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Std.Usize.wrapping_add column 1#usize))
      pure (cont (c1_columns_inactive_balanced1, column1)))
  else
    pure (done c1_columns_inactive_balanced)

theorem erase_program (ops : ExternalFuns)
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (masks : Array Std.U16 64#usize) (c1_columns_inactive_balanced : Std.Usize)
  (column : Std.Usize) :
  erase ops (program c1 masks c1_columns_inactive_balanced column) =
    @prover.audit_masks_loop0.body _ ops c1 masks c1_columns_inactive_balanced column := by
  unfold program prover.audit_masks_loop0.body
  try dsimp only
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro v
      try dsimp only
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro m
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro m1
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro b
            rw [PV_W_StructuredBinds.erase_join]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              try dsimp only
              apply PV_W_Callbacks.erase_if_congr
              ·
                rfl
              ·
                rfl
            · intro c1_columns_inactive_balanced1
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro column1
                rfl
  ·
    rfl

#print axioms erase_program
end R1Z.PV_W_R_AuditMasksBody0
