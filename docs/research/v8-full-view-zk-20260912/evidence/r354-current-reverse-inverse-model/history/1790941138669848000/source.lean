import AspisV8R19.R350AfterGuardsExecution
import AspisV8R19.R341PrefixNonzero

/-! Symbolic inverse identities for the already source-bound reverse recurrence.
No source guard, traversal, Std or compiler premise is added. -/
set_option autoImplicit false
namespace AspisV8R19.R354ReverseInverseModel
open Aeneas Aeneas.Std
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R341PrefixNonzero
open AspisV8R19.R311BatchReverseLoopExecution
open AspisV8R19.R342OutputSetup
open AspisV8R19.R350AfterGuardsExecution
noncomputable section

theorem product_inverse_times_right (p q : M31Exact) (hq : q ≠ 0) :
    (p * q)⁻¹ * q = p⁻¹ := by
  rw [mul_inv_rev]
  calc
    q⁻¹ * p⁻¹ * q = (q⁻¹ * q) * p⁻¹ := by ring
    _ = p⁻¹ := by rw [inv_mul_cancel₀ hq, one_mul]

theorem left_times_product_inverse (p q : M31Exact) (hp : p ≠ 0) :
    p * (p * q)⁻¹ = q⁻¹ := by
  rw [mul_inv_rev]
  calc
    p * (q⁻¹ * p⁻¹) = (p * p⁻¹) * q⁻¹ := by ring
    _ = q⁻¹ := by rw [mul_inv_cancel₀ hp, one_mul]

/-- The descending recurrence never changes an index above its count. -/
theorem reverseModel_above_count (f g : Nat → M31Exact) (n : Nat)
    (x : M31Exact) (out : VecU32) (k : Nat) (hk : n < k) :
    (reverseModel f g n x out).2.val[k]? = out.val[k]? := by
  induction n generalizing x out with
  | zero => rfl
  | succ n ih =>
      change (reverseModel f g n (x * f (n + 1))
        (setNat out (n + 1) (encodeBase (g n * x)))).2.val[k]? = out.val[k]?
      rw [ih _ _ (by omega)]
      change (out.val.set (n + 1) (encodeBase (g n * x)))[k]? = out.val[k]?
      exact List.getElem?_set_ne (by omega)

/-- At each descending step, the saved value is the corresponding inverse and
its updated accumulator is the inverse of the preceding prefix. -/
theorem reverseModel_inverse_step (f : Nat → M31Exact) (n : Nat) (out : VecU32)
    (hp : sourcePrefixValue f n ≠ 0) (hn : f (n + 1) ≠ 0) :
    reverseModel f (sourcePrefixValue f) (n + 1)
      (sourcePrefixValue f (n + 1))⁻¹ out =
    reverseModel f (sourcePrefixValue f) n (sourcePrefixValue f n)⁻¹
      (setNat out (n + 1) (encodeBase (f (n + 1))⁻¹)) := by
  rw [reverseModel, sourcePrefixValue_succ,
    product_inverse_times_right _ _ hn, left_times_product_inverse _ _ hp]

theorem reverseModel_inverse_accumulator (f : Nat → M31Exact) (n : Nat)
    (out : VecU32) (hn : ∀ k, k ≤ n → f k ≠ 0) :
    (reverseModel f (sourcePrefixValue f) n (sourcePrefixValue f n)⁻¹ out).1 =
      (f 0)⁻¹ := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
      rw [reverseModel_inverse_step f n out
        ((sourcePrefixValue_ne_zero_iff f n).mpr (fun k hk => hn k (by omega)))
        (hn (n + 1) (by omega))]
      exact ih _ (fun k hk => hn k (by omega))

theorem reverseModel_inverse_read (f : Nat → M31Exact) (n : Nat)
    (out : VecU32) (hn : ∀ k, k ≤ n → f k ≠ 0)
    (hcapacity : n < out.val.length) (k : Nat) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (reverseModel f (sourcePrefixValue f) n (sourcePrefixValue f n)⁻¹ out).2.val[k]? =
      some (encodeBase (f k)⁻¹) := by
  induction n generalizing out with
  | zero => omega
  | succ n ih =>
      rw [reverseModel_inverse_step f n out
        ((sourcePrefixValue_ne_zero_iff f n).mpr (fun j hj => hn j (by omega)))
        (hn (n + 1) (by omega))]
      by_cases hlow : k ≤ n
      · apply ih _ (fun j hj => hn j (by omega)) _ hlow
        change n < (out.val.set (n + 1) _).length
        rw [List.length_set]
        omega
      · have hk : k = n + 1 := by omega
        subst k
        rw [reverseModel_above_count _ _ n _ _ (n + 1) (by omega)]
        change (out.val.set (n + 1) (encodeBase (f (n + 1))⁻¹))[n + 1]? = _
        exact List.getElem?_set_self hcapacity

theorem sourceOutput_inverse_read (xs : Slice U32) (f : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hf : ∀ j, j < xs.val.length → f j ≠ 0)
    (j : Nat) (hj : j < xs.val.length) :
    (sourceOutput xs f (sourcePrefixValue f (xs.val.length - 1))⁻¹).val[j]? =
      some (encodeBase (f j)⁻¹) := by
  have hn : ∀ k, k ≤ xs.val.length - 1 → f k ≠ 0 :=
    fun k hk => hf k (by omega)
  have hm := reverseModel_inverse_accumulator f (xs.val.length - 1) (zeroVec xs) hn
  have hlen : (reverseModel f (sourcePrefixValue f) (xs.val.length - 1)
      (sourcePrefixValue f (xs.val.length - 1))⁻¹ (zeroVec xs)).2.val.length =
      xs.val.length :=
    (reverseModel_output_length _ _ _ _ _).trans (zeroVec_length xs)
  unfold sourceOutput
  by_cases hz : j = 0
  · subst j
    change (_ .val.set 0 _)[0]? = _
    rw [List.getElem?_set_self (by rw [hlen]; exact hx), hm]
  · change (_ .val.set 0 _)[j]? = _
    rw [List.getElem?_set_ne (by omega)]
    exact reverseModel_inverse_read f (xs.val.length - 1) (zeroVec xs) hn
      (by rw [zeroVec_length]; omega) j (by omega) (by omega)

#print axioms product_inverse_times_right
#print axioms left_times_product_inverse
#print axioms reverseModel_above_count
#print axioms reverseModel_inverse_step
#print axioms reverseModel_inverse_accumulator
#print axioms reverseModel_inverse_read
#print axioms sourceOutput_inverse_read
end
end AspisV8R19.R354ReverseInverseModel
