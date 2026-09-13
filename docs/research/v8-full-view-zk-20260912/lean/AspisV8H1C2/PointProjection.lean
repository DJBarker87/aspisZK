import Mathlib.Data.Fin.Basic

/-! Literal 3*28 projection from three 29-column serialized point rows.
All three omitted D entries remain public. -/
set_option autoImplicit false
namespace AspisV8H1C2

def pointSourceIndex (r : Fin 3) (c : Fin 28) : Nat :=
  271 + r.val * 29 + c.val

theorem pointSourceIndex_bounds (r : Fin 3) (c : Fin 28) :
    271 ≤ pointSourceIndex r c ∧ pointSourceIndex r c < 358 := by
  have hr := r.isLt
  have hc := c.isLt
  unfold pointSourceIndex
  omega

theorem pointSourceIndex_not_D (r : Fin 3) (c : Fin 28) :
    pointSourceIndex r c ≠ 299 ∧ pointSourceIndex r c ≠ 328 ∧
      pointSourceIndex r c ≠ 357 := by
  have hr := r.isLt
  have hc := c.isLt
  unfold pointSourceIndex
  omega

theorem pointSourceIndex_injective :
    Function.Injective (fun rc : Fin 3 × Fin 28 => pointSourceIndex rc.1 rc.2) := by
  rintro ⟨ar,ac⟩ ⟨br,bc⟩ h
  have har := ar.isLt
  have hbr := br.isLt
  have hac := ac.isLt
  have hbc := bc.isLt
  simp only [pointSourceIndex] at h
  have hr : ar.val = br.val := by omega
  have hc : ac.val = bc.val := by omega
  exact Prod.ext (Fin.ext hr) (Fin.ext hc)

#print axioms pointSourceIndex_bounds
#print axioms pointSourceIndex_not_D
#print axioms pointSourceIndex_injective
end AspisV8H1C2
