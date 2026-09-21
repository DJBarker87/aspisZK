import AspisV8R17.LegalMaskCoordinates
import AspisV8R17.SourceMixing

/-! Carry the source balancing equation through the COMPLETE mixing map.
The 271-coordinate prefix alone is never treated as an unrestricted law. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2147483647]

def mixedBalanceConstraint (inactive : Finset (Fin 1024)) (coins : Fin 1024 → F) : F :=
  ∑ i ∈ inactive, (mixing1024 (F := F)).symm coins i

def balancedMixEquiv (inactive : Finset (Fin 1024)) :
    {g : Fin 1024 → F // ∑ i ∈ inactive, g i = 0} ≃
      {coins : Fin 1024 → F // mixedBalanceConstraint inactive coins = 0} where
  toFun g := ⟨mixing1024 g.val, by simpa [mixedBalanceConstraint] using g.property⟩
  invFun coins := ⟨(mixing1024 (F := F)).symm coins.val, coins.property⟩
  left_inv g := by apply Subtype.ext; exact (mixing1024 (F := F)).symm_apply_apply g.val
  right_inv coins := by apply Subtype.ext; exact (mixing1024 (F := F)).apply_symm_apply coins.val

def legalSourceMixing (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (hp : pivot ∈ inactive) :
    ({i : Fin 1024 // i ≠ pivot} → F) ≃
      {coins : Fin 1024 → F // mixedBalanceConstraint inactive coins = 0} :=
  (legalMaskEquiv inactive pivot hp).trans (balancedMixEquiv inactive)

theorem legalSourceMixing_horner (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (hp : pivot ∈ inactive) (free : {i : Fin 1024 // i ≠ pivot} → F) (i : Fin 1024) :
    (legalSourceMixing inactive pivot hp free).val i =
      sourceMixHorner ((i.val+1 : ℕ) : F)
        (List.ofFn (legalMaskEquiv inactive pivot hp free).val) := by
  exact (sourceMixHorner_eq_mixing1024 (legalMaskEquiv inactive pivot hp free).val i).symm

theorem mixing1024_add (u v : Fin 1024 → F) :
    mixing1024 (u+v) = mixing1024 u + mixing1024 v := by
  funext i
  change mix (publicNodes F 1024) (u+v) i =
    mix (publicNodes F 1024) u i + mix (publicNodes F 1024) v i
  simp only [mix_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem mixing1024_symm_add (u v : Fin 1024 → F) :
    (mixing1024 (F := F)).symm (u+v) =
      (mixing1024 (F := F)).symm u + (mixing1024 (F := F)).symm v := by
  apply (mixing1024 (F := F)).injective
  rw [mixing1024_add]
  simp

theorem mixedBalanceConstraint_add (inactive : Finset (Fin 1024)) (u v : Fin 1024 → F) :
    mixedBalanceConstraint inactive (u+v) =
      mixedBalanceConstraint inactive u + mixedBalanceConstraint inactive v := by
  simp [mixedBalanceConstraint, mixing1024_symm_add, Finset.sum_add_distrib]

theorem mixed_correction_legal_iff (inactive : Finset (Fin 1024))
    (coins delta : Fin 1024 → F) (legal : mixedBalanceConstraint inactive coins = 0) :
    mixedBalanceConstraint inactive (coins+delta) = 0 ↔
      mixedBalanceConstraint inactive delta = 0 := by
  rw [mixedBalanceConstraint_add, legal, zero_add]

#print axioms balancedMixEquiv
#print axioms legalSourceMixing
#print axioms legalSourceMixing_horner
#print axioms mixing1024_add
#print axioms mixing1024_symm_add
#print axioms mixedBalanceConstraint_add
#print axioms mixed_correction_legal_iff
end
end AspisV8R17
