import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_InactiveSumBody
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize)
  (sum : aspis_core.field.QM31) (row : Std.Usize) :
  P (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31) := do
  let i := Slice.len values
  if row < i then
    let i1 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_shr row 4#u32))
    let i2 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize masks i1)
    let i3 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (row &&& 15#usize))
    let i4 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.U16.wrapping_shl 1#u16 (UScalar.cast .U32 i3)))
    let i5 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (i2 &&& i4))
    PV_W_StructuredBinds.join (do
      if i5 = 0#u16 then
        let q ← invoke "Slice.index_usize" (fun ops =>
            letI : ExternalFuns := ops
            Slice.index_usize values row)
        invoke "aspis_core.field.QM31.add" (fun ops =>
          letI : ExternalFuns := ops
          aspis_core.field.QM31.add sum q)
      else
        pure sum) (fun sum1 => do
      let row1 ← invoke "Aeneas.Std.lift" (fun ops =>
          letI : ExternalFuns := ops
          Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize))
      pure (cont (sum1, row1)))
  else
    pure (done sum)

theorem erase_program (ops : ExternalFuns)
  (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize)
  (sum : aspis_core.field.QM31) (row : Std.Usize) :
  erase ops (program values masks sum row) =
    @prover.inactive_sum_k_loop.body _ ops values masks sum row := by
  unfold program prover.inactive_sum_k_loop.body
  try dsimp only
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro i1
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro i2
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro i3
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro i4
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro i5
              rw [PV_W_StructuredBinds.erase_join]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                try dsimp only
                apply PV_W_Callbacks.erase_if_congr
                ·
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro q
                    exact erase_invoke ops _ _
                ·
                  rfl
              · intro sum1
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro row1
                  rfl
  ·
    rfl

#print axioms erase_program
end R1Z.PV_W_R_InactiveSumBody
