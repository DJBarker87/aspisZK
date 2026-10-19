import AspisFormal.CircleGroupOrder

set_option autoImplicit false

namespace R1ZBatchInverseAlgebraV3

variable {K : Type*} [Field K]

theorem inv_product_mul_left_cancel (a x : K) (ha : a ≠ 0) (hx : x ≠ 0) :
    (a * x)⁻¹ * a = x⁻¹ := by
  calc
    (a * x)⁻¹ * a = (a⁻¹ * a) * x⁻¹ := by rw [mul_inv]; ac_rfl
    _ = x⁻¹ := by simp [ha]

theorem inv_product_update (a x : K) (ha : a ≠ 0) (hx : x ≠ 0) :
    (a * x)⁻¹ * x = a⁻¹ := by
  calc
    (a * x)⁻¹ * x = (x⁻¹ * x) * a⁻¹ := by rw [mul_inv]; ac_rfl
    _ = a⁻¹ := by simp [hx]

theorem list_take_succ_eq (xs : List K) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simp [ih (i := i)]

theorem list_take_succ_prod (xs : List K) (i : Nat) (hi : i < xs.length) :
    (xs.take (i + 1)).prod = (xs.take i).prod * xs[i] := by
  rw [list_take_succ_eq xs i hi, List.prod_append]
  simp

theorem reverse_pass_output_is_inverse (xs : List K) (i : Nat) (hi : i < xs.length)
    (hpre : (xs.take i).prod ≠ 0) (hxi : xs[i] ≠ 0) :
    ((xs.take (i + 1)).prod)⁻¹ * (xs.take i).prod = (xs[i])⁻¹ := by
  rw [list_take_succ_prod xs i hi]
  exact inv_product_mul_left_cancel _ _ hpre hxi


/-- Finite reverse pass: at stage n, s is the inverse of the product of the
first n inputs. The next visit writes at index n-1 and updates s by that input. -/
def backwards (xs : List K) : Nat → K → List K
  | 0, _ => []
  | n + 1, s =>
      backwards xs n (s * xs.getD n 1) ++ [s * (xs.take n).prod]

theorem backwards_correct (xs : List K) (n : Nat) (hn : n ≤ xs.length)
    (hnz : ∀ m, m ≤ n → (xs.take m).prod ≠ 0)
    (s : K) (hs : s = (xs.take n).prod⁻¹) :
    backwards xs n s = (xs.take n).map Inv.inv := by
  induction n generalizing s with
  | zero => simp [backwards]
  | succ n ih =>
    have hlt : n < xs.length := by omega
    have htake := list_take_succ_prod xs n hlt
    have hx : xs[n] ≠ 0 := by
      intro hzero
      have hz := hnz (n + 1) (by omega)
      rw [htake] at hz
      simp [hzero] at hz
    have ha : (xs.take n).prod ≠ 0 := hnz n (by omega)
    have hget : xs.getD n 1 = xs[n] := by simp [hlt]
    have hs' : s * xs[n] = (xs.take n).prod⁻¹ := by
      rw [hs, htake]
      exact inv_product_update _ _ ha hx
    have hrec := ih (hn := by omega) (hnz := fun m hm => hnz m (by omega))
      (s := s * xs[n]) hs'
    have hlist := list_take_succ_eq xs n hlt
    have hout : s * (xs.take n).prod = xs[n]⁻¹ := by
      rw [hs]
      exact reverse_pass_output_is_inverse xs n hlt ha hx
    rw [backwards, hget, hrec, hlist, List.map_append]
    simp only [List.map_singleton]
    rw [hout]


#print axioms backwards_correct
#print axioms reverse_pass_output_is_inverse

end R1ZBatchInverseAlgebraV3
