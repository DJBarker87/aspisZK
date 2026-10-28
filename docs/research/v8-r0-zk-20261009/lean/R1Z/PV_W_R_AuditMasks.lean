import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_AuditMasks
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize) :
  P prover.MaskedFixtureAudit := do
  let c1_columns_inactive_balanced ← invoke "prover.audit_masks_loop0" (fun ops =>
      letI : ExternalFuns := ops
      prover.audit_masks_loop0 c1 masks 0#usize 0#usize)
  let mask_only_columns_inactive_balanced ← invoke "prover.audit_masks_loop1" (fun ops =>
      letI : ExternalFuns := ops
      prover.audit_masks_loop1 mask_only masks 0#usize 0#usize)
  let s ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice d))
  let q ← invoke "prover.inactive_sum_k" (fun ops =>
      letI : ExternalFuns := ops
      prover.inactive_sum_k s masks)
  let q1 ← invoke "aspis_core.field.QM31.ZERO" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.QM31.ZERO)
  let b ← invoke "aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q1)
  let s1 ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice g))
  let q2 ← invoke "prover.inactive_sum_k" (fun ops =>
      letI : ExternalFuns := ops
      prover.inactive_sum_k s1 masks)
  let b1 ← invoke "aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q2 q1)
  let s2 ← invoke "Aeneas.Std.lift" (fun ops =>
      letI : ExternalFuns := ops
      Aeneas.Std.lift (Array.to_slice h1_padding))
  let q3 ← invoke "prover.inactive_sum_k" (fun ops =>
      letI : ExternalFuns := ops
      prover.inactive_sum_k s2 masks)
  let b2 ← invoke "aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q3 q1)
  pure {
    c1_columns_inactive_balanced,
    mask_only_columns_inactive_balanced,
    d_inactive_balanced := b,
    g_inactive_balanced := b1,
    h1_padding_inactive_balanced := b2,
    h1_total_balanced := true
    }

theorem erase_program (ops : ExternalFuns)
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize) :
  erase ops (program c1 mask_only d g h1_padding masks) =
    @prover.audit_masks _ ops c1 mask_only d g h1_padding masks := by
  unfold program prover.audit_masks
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro c1_columns_inactive_balanced
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro mask_only_columns_inactive_balanced
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro s
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro q
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro q1
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro b
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro s1
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro q2
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro b1
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro s2
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro q3
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro b2
                          rfl

#print axioms erase_program
end R1Z.PV_W_R_AuditMasks
