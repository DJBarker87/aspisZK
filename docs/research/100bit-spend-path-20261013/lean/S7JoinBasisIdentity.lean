import AspisFormal.V5FriNaturalBasisRadix4

/-! Total field reference for the production basis. Source array linkage is
proved separately; this module does not identify a supplied array by fiat. -/
set_option autoImplicit false
namespace AspisR1.S7JoinBasisIdentity
open AspisCircleTensorBinding AspisV5FriNaturalBasisRadix4
variable {K : Type*} [CommRing K]

/-- Six factors, selected by the low six bits, in the source's level order. -/
def value : Nat → K → Nat → K
  | 0, _, _ => 1
  | n+1, x, j => (if j%2=0 then 1 else x) * value n (2*x^2-1) (j/2)

theorem value_eq_natural (n : Nat) (x : K) (j : Nat) (hj : j<2^n) :
    value n x j = naturalLineValue x j := by
  induction n generalizing x j with
  | zero =>
      have : j=0 := by simpa only [pow_zero, Nat.lt_one_iff] using hj
      subst j
      simp [value,naturalLineValue]
  | succ n ih =>
      have hdiv : j/2<2^n := by rw [pow_succ] at hj; omega
      have hm := Nat.mod_lt j (by decide : 0<2)
      by_cases even : j%2=0
      · have he : j=2*(j/2) := by omega
        rw [value,if_pos even,one_mul,ih _ _ hdiv]
        conv_rhs => rw [he, naturalLineValue_two_mul]
        rfl
      · have he : j=2*(j/2)+1 := by omega
        rw [value,if_neg even,ih _ _ hdiv]
        conv_rhs => rw [he, naturalLineValue_two_mul_add_one]
        rfl

theorem production_basis (x : K) (j : Fin 64) :
    value 6 x j.val=naturalLineValue x j.val :=
  value_eq_natural 6 x j.val j.isLt

#print axioms value_eq_natural
#print axioms production_basis
end AspisR1.S7JoinBasisIdentity
