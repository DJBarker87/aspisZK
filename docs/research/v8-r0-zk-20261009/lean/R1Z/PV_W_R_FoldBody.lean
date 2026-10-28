import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_R_FoldCell
open Aeneas.Std.ControlFlow
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_R_FoldBody
open Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]

def program
  (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool)
  (out : alloc.vec.Vec aspis_core.field.wide_exact.WideExact) (i : Std.Usize) :
  P (ControlFlow ((alloc.vec.Vec aspis_core.field.wide_exact.WideExact) ×
    Std.Usize) (alloc.vec.Vec aspis_core.field.wide_exact.WideExact)) := do
  let i1 := Slice.len q
  let i2 ← invoke "i1" (fun ops =>
      letI : ExternalFuns := ops
      i1 / 4#usize)
  if i < i2 then
    let i3 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i))
    let we ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize q i3)
    let i4 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i))
    let i5 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add i4 1#usize))
    let we1 ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize q i5)
    let i6 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i))
    let i7 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add i6 2#usize))
    let we2 ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize q i7)
    let i8 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i))
    let i9 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add i8 3#usize))
    let we3 ← invoke "Slice.index_usize" (fun ops =>
        letI : ExternalFuns := ops
        Slice.index_usize q i9)
    let value ← PV_W_R_FoldCell.program (Array.make 4#usize [ we, we1, we2, we3 ]) alpha dual
    let out1 ← invoke "alloc.vec.Vec.push" (fun ops =>
        letI : ExternalFuns := ops
        alloc.vec.Vec.push out value)
    let i10 ← invoke "Aeneas.Std.lift" (fun ops =>
        letI : ExternalFuns := ops
        Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize))
    pure (cont (out1, i10))
  else
    pure (done out)

theorem erase_program (ops : ExternalFuns)
  (q : Slice aspis_core.field.wide_exact.WideExact)
  (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool)
  (out : alloc.vec.Vec aspis_core.field.wide_exact.WideExact) (i : Std.Usize) :
  erase ops (program q alpha dual out i) =
    @prover.fold_loop.body _ ops q alpha dual out i := by
  unfold program prover.fold_loop.body
  try dsimp only
  try dsimp only
  rw [erase_bind]
  apply PV_W_RecursiveLaws.bind_congr
  ·
    exact erase_invoke ops _ _
  · intro i2
    try dsimp only
    apply PV_W_Callbacks.erase_if_congr
    ·
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
        · intro we
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
                · intro i6
                  try dsimp only
                  rw [erase_bind]
                  apply PV_W_RecursiveLaws.bind_congr
                  ·
                    exact erase_invoke ops _ _
                  · intro i7
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
                      · intro i8
                        try dsimp only
                        rw [erase_bind]
                        apply PV_W_RecursiveLaws.bind_congr
                        ·
                          exact erase_invoke ops _ _
                        · intro i9
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
                              rw [PV_W_R_FoldCell.erase_program]
                            · intro value
                              try dsimp only
                              rw [erase_bind]
                              apply PV_W_RecursiveLaws.bind_congr
                              ·
                                exact erase_invoke ops _ _
                              · intro out1
                                try dsimp only
                                rw [erase_bind]
                                apply PV_W_RecursiveLaws.bind_congr
                                ·
                                  exact erase_invoke ops _ _
                                · intro i10
                                  rfl
    ·
      rfl

#print axioms erase_program
end R1Z.PV_W_R_FoldBody
