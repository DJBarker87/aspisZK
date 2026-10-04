import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R551SplitCheck
def splitFin8Four {A : Type} : (Fin 8 → A) ≃ ((Fin 4 → A) × (Fin 4 → A)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨4 + j.val, by omega⟩)
  invFun p i := if h : i.val < 4 then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - 4, by omega⟩
  left_inv f := by
    funext i
    dsimp
    split
    · rfl
    · apply congrArg f
      apply Fin.ext
      have hi := i.isLt
      omega
  right_inv p := by
    apply Prod.ext
    · funext j
      dsimp
      simp only [dif_pos j.isLt]
    · funext j
      dsimp
      have hj : ¬ 4 + j.val < 4 := by omega
      simp only [dif_neg hj]
      apply congrArg p.2
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
#print axioms splitFin8Four
end AspisV8R19.R551SplitCheck
