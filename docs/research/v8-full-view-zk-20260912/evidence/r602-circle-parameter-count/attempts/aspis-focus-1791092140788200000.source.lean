import AspisV8R19.R445InitialBlockRejectionLaw
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace AspisV8R19.R602CircleParameterCount
open AspisV8R19.R445InitialBlockRejectionLaw (modulus)
noncomputable section

def finZero {p : Nat} (hp : 0 < p) : Fin p := ⟨0, hp⟩

def fixedTailEquiv {p : Nat} (z : Fin p) :
    {x : Fin 4 → Fin p // x 2 = z ∧ x 3 = z} ≃ (Fin 2 → Fin p) where
  toFun x := ![x.1 0, x.1 1]
  invFun y := ⟨![y 0, y 1, z, z], by constructor <;> simp⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [x.2]
  right_inv := by
    intro y
    funext i
    fin_cases i <;> rfl

theorem circle_parameter_count (p : Nat) (hp : 0 < p) :
    (Finset.univ.filter (fun x : Fin 4 → Fin p =>
      x 2 ≠ finZero hp ∨ x 3 ≠ finZero hp)).card =
      p^4 - p^2 := by
  classical
  let z : Fin p := finZero hp
  let bad : Finset (Fin 4 → Fin p) :=
    Finset.univ.filter (fun x => x 2 = z ∧ x 3 = z)
  have hbad : bad.card = p^2 := by
    have heq : Fintype.card bad =
        Fintype.card (Fin 2 → Fin p) :=
      by simpa [bad] using Fintype.card_congr (fixedTailEquiv z)
    have hcard : bad.card = Fintype.card bad := (Fintype.card_coe bad).symm
    rw [hcard, heq]
    simp [Fintype.card_fun]
  let pred : (Fin 4 → Fin p) → Prop := fun x => x 2 ≠ z ∨ x 3 ≠ z
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4 → Fin p))) (p := pred)
  have hnot : Finset.univ.filter (fun x : Fin 4 → Fin p => ¬ pred x) = bad := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad, pred]
    constructor
    · intro h
      constructor
      · exact not_ne_iff.mp (not_or.mp h).1
      · exact not_ne_iff.mp (not_or.mp h).2
    · rintro ⟨h2,h3⟩ h
      rcases h with hn | hn
      · exact hn h2
      · exact hn h3
  rw [hnot, hbad, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hpart
  omega

theorem selected_circle_parameter_count :
    (Finset.univ.filter (fun x : Fin 4 → Fin modulus => x 2 ≠ 0 ∨ x 3 ≠ 0)).card =
      modulus^4 - modulus^2 :=
  circle_parameter_count modulus (by norm_num [modulus])

#print axioms fixedTailEquiv
#print axioms circle_parameter_count
#print axioms selected_circle_parameter_count
end
end AspisV8R19.R602CircleParameterCount
