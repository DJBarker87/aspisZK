import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_FoldCell
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (h : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool) :
  P aspis_core.field.wide_exact.WideExact := do
  if dual then
    let we ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 0#usize)
    let we1 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 3#usize)
    let we2 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 2#usize)
    let we3 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 1#usize)
    let we4 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we3)
    let we5 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add we2 we4)
    let we6 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we5)
    let we7 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add we1 we6)
    let we8 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we7)
    let we9 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add we we8)
    invoke "aspis_core.field.wide_exact.WideExact.mul_m31" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.wide_exact.WideExact.mul_m31 we9 weights.QUARTER)
  else
    let we ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 0#usize)
    let we1 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 1#usize)
    let we2 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 2#usize)
    let we3 ← invoke "Array.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Array.index_usize h 3#usize)
    let we4 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we3)
    let we5 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add we2 we4)
    let we6 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we5)
    let we7 ← invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.add we1 we6)
    let we8 ← invoke "aspis_core.field.wide_exact.WideExact.mul" (fun ops =>
        letI : ExternalFuns := ops
        aspis_core.field.wide_exact.WideExact.mul alpha we7)
    invoke "aspis_core.field.wide_exact.WideExact.add" (fun ops =>
      letI : ExternalFuns := ops
      aspis_core.field.wide_exact.WideExact.add we we8)

theorem erase_program (ops : ExternalFuns)
  (h : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool) :
  erase ops (program h alpha dual) =
    @prover.fold_cell _ ops h alpha dual := by
  unfold program prover.fold_cell
  try dsimp only
  apply PV_W_Callbacks.erase_if_congr
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro we
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro we1
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro we2
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro we3
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro we4
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro we5
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro we6
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro we7
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro we8
                      try dsimp only
                      rw [erase_bind]
                      apply PV_W_RecursiveLaws.bind_congr
                      ·
                        exact erase_invoke ops _ _
                      · intro we9
                        exact erase_invoke ops _ _
  ·
    try dsimp only
    rw [erase_bind]
    apply PV_W_RecursiveLaws.bind_congr
    ·
      exact erase_invoke ops _ _
    · intro we
      try dsimp only
      rw [erase_bind]
      apply PV_W_RecursiveLaws.bind_congr
      ·
        exact erase_invoke ops _ _
      · intro we1
        try dsimp only
        rw [erase_bind]
        apply PV_W_RecursiveLaws.bind_congr
        ·
          exact erase_invoke ops _ _
        · intro we2
          try dsimp only
          rw [erase_bind]
          apply PV_W_RecursiveLaws.bind_congr
          ·
            exact erase_invoke ops _ _
          · intro we3
            try dsimp only
            rw [erase_bind]
            apply PV_W_RecursiveLaws.bind_congr
            ·
              exact erase_invoke ops _ _
            · intro we4
              try dsimp only
              rw [erase_bind]
              apply PV_W_RecursiveLaws.bind_congr
              ·
                exact erase_invoke ops _ _
              · intro we5
                try dsimp only
                rw [erase_bind]
                apply PV_W_RecursiveLaws.bind_congr
                ·
                  exact erase_invoke ops _ _
                · intro we6
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro we7
                    try dsimp only
                    rw [erase_bind]
                    apply PV_W_RecursiveLaws.bind_congr
                    ·
                      exact erase_invoke ops _ _
                    · intro we8
                      exact erase_invoke ops _ _

#print axioms erase_program
end R1Z.PV_W_R_FoldCell
