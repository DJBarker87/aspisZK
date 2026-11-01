import NEG_DotDomain
set_option autoImplicit false
namespace NEG_Induction
open NEG_DotDomain
/-- Arbitrarily many bounded product choices; no solver-selected log is fixed. -/
theorem products (xs : List Nat) (h : ∀ x∈xs, x≤B) : xs.sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul]
    omega

theorem batch (xs : List Nat) (h : ∀ x∈xs, x≤B) (len : xs.length≤4) :
    xs.sum < 2^64 := by
  have hs := products xs h
  have hl := Nat.mul_le_mul_right B len
  norm_num [B] at hs hl ⊢
  omega

theorem folds (xs : List Nat) (h : ∀ x∈xs, x<2^34) :
    xs.sum ≤ xs.length*(2^34-1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul]
    omega

theorem seven_batches (xs : List Nat) (h : ∀ x∈xs, x<2^34) (len : xs.length≤7) :
    xs.sum < 2^37 := by
  have hs := folds xs h
  have hl := Nat.mul_le_mul_right (2^34-1) len
  norm_num at hs hl ⊢
  omega

/-- Exact per-site instantiation of every free product in a finite log. -/
theorem canonical_products (a b : List Nat) (same : a.length=b.length)
    (ha : ∀ x∈a,x<P) (hb : ∀ x∈b,x<P) :
    ∀ p∈List.zipWith (·*·) a b,p≤B := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have rest := ih ys (by simpa using same)
        (by intro z hz;exact ha z (by simp [hz]))
        (by intro z hz;exact hb z (by simp [hz]))
      intro p hp
      simp only [List.zipWith_cons_cons,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact instantiate x y hx hy
      · exact rest p hp
#print axioms products
#print axioms batch
#print axioms folds
#print axioms seven_batches
#print axioms canonical_products
end NEG_Induction
