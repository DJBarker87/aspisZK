import AspisV8R19.NormalizedQuerySection

/-! Add the public root 1 to the normalized query section. This makes the
low repair invisible to a constant low functional, rather than assuming it
is zero. The concrete two-swap source low map and nonzero matrix certificate
are separate obligations. No oracle law or privacy conclusion is asserted. -/
set_option autoImplicit false
namespace AspisR19.AugmentedQuerySection
open AspisCircleTensorBinding Polynomial
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def roots (t : Fin 22 → F) : Fin 23 → F := Fin.cases 1 t

theorem roots_injective (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) : Function.Injective (roots t) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h; exact (noneOne j (by simpa [roots] using h.symm)).elim
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h; exact (noneOne i (by simpa [roots] using h)).elim
    · intro h
      exact congrArg Fin.succ (ht (by simpa [roots] using h))

omit [NeZero (2 : F)] in
theorem doubled_one (n : Nat) : doubledFactor (1 : F) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [doubledFactor,ih]; ring

omit [NeZero (2 : F)] in
theorem natural_one (n : Nat) : naturalLineValue (1 : F) n = 1 := by
  simp [naturalLineValue,doubled_one]

def low (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) : Fin 23 → F :=
  Classical.choose (AspisV8R16.natural_eval_surjective (roots t)
    (roots_injective t ht noneOne)
    (fun i => (naturalLinePoly F d.val).eval (roots t i)))

theorem low_evaluates (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) :
    (naturalEvalMatrix F 23 (roots t)).mulVec (low t ht noneOne d) =
      fun i => (naturalLinePoly F d.val).eval (roots t i) :=
  Classical.choose_spec (AspisV8R16.natural_eval_surjective (roots t)
    (roots_injective t ht noneOne) _)

theorem low_sum_one (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) :
    ∑ i, low t ht noneOne d i = 1 := by
  have h := congrFun (low_evaluates t ht noneOne d) 0
  simpa [Matrix.mulVec,dotProduct,naturalEvalMatrix,roots,
    ← naturalLineValue_eq_eval,natural_one] using h

def extendLow (r : Fin 23 → F) (i : Fin 32) : F :=
  if h : i.val < 23 then r ⟨i.val,h⟩ else 0

def normalized (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d i : Fin 32) : F :=
  (if i=d then 1 else 0) - extendLow (low t ht noneOne d) i

omit [NeZero (2 : F)] in
theorem extendLow_sum (r : Fin 23 → F) (w : Fin 32 → F) :
    ∑ i, extendLow r i * w i = ∑ j : Fin 23, r j * w ⟨j.val,by omega⟩ := by
  rw [Fin.sum_univ_add (a := 23) (b := 9)]
  simp [extendLow,Fin.castAdd,Fin.natAdd,Fin.castLE]

theorem normalized_high (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d i : Fin 32) (hi : 23 ≤ i.val) :
    normalized t ht noneOne d i = if i=d then 1 else 0 := by
  simp [normalized,extendLow,show ¬i.val < 23 by omega]

theorem normalized_evaluation (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) (x : F) :
    NormalizedQuerySection.evaluate (normalized t ht noneOne d) x =
      naturalLineValue x d.val -
        ∑ i : Fin 23, low t ht noneOne d i * naturalLineValue x i.val := by
  simp only [NormalizedQuerySection.evaluate,normalized,sub_mul,Finset.sum_sub_distrib]
  rw [extendLow_sum]
  simp

theorem normalized_augmented_root (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) (j : Fin 23) :
    NormalizedQuerySection.evaluate (normalized t ht noneOne d) (roots t j) = 0 := by
  have h := congrFun (low_evaluates t ht noneOne d) j
  simp only [Matrix.mulVec,dotProduct,naturalEvalMatrix] at h
  rw [normalized_evaluation]
  simp only [naturalLineValue_eq_eval]
  rw [show (∑ i : Fin 23, low t ht noneOne d i * (naturalLinePoly F i.val).eval (roots t j)) =
      (naturalLinePoly F d.val).eval (roots t j) by simpa [mul_comm] using h]
  exact sub_self _

theorem normalized_query_root (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) (j : Fin 22) :
    NormalizedQuerySection.evaluate (normalized t ht noneOne d) (t j) = 0 := by
  simpa [roots] using normalized_augmented_root t ht noneOne d j.succ

theorem normalized_sum_zero (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) :
    ∑ i, normalized t ht noneOne d i = 0 := by
  simpa [roots,NormalizedQuerySection.evaluate,natural_one] using
    normalized_augmented_root t ht noneOne d 0

/-- Exact repair transport for a constant, not necessarily zero, low map. -/
theorem constant_low_transport (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (d : Fin 32) (w : Fin 32 → F)
    (hw : ∀ i, i.val < 23 → w i = w 0) :
    (∑ i, normalized t ht noneOne d i * w i) = w d - w 0 := by
  have hs : (∑ i : Fin 23, low t ht noneOne d i * w ⟨i.val,by omega⟩) =
      (∑ i, low t ht noneOne d i) * w 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw _ i.isLt]
  simp only [normalized,sub_mul,Finset.sum_sub_distrib]
  rw [extendLow_sum,hs,low_sum_one]
  simp

/-- The additional public root is excluded by the existing nonzero-y domain
condition on a unit-circle point. Its source instantiation remains explicit. -/
theorem line_root_ne_one (x y : F) (circle : x*x+y*y=1) (hy : y≠0) :
    2*x*x-1≠1 := by
  intro h
  have he : 2*(x*x-1)=0 := by linear_combination h
  have hx : x*x-1=0 := (mul_eq_zero.mp he).resolve_left (NeZero.ne (2:F))
  have hyy : y*y=0 := by linear_combination circle - hx
  exact hy (mul_self_eq_zero.mp hyy)

#print axioms roots_injective
#print axioms doubled_one
#print axioms natural_one
#print axioms low_evaluates
#print axioms low_sum_one
#print axioms extendLow_sum
#print axioms normalized_high
#print axioms normalized_evaluation
#print axioms normalized_augmented_root
#print axioms normalized_query_root
#print axioms normalized_sum_zero
#print axioms constant_low_transport
#print axioms line_root_ne_one
end
end AspisR19.AugmentedQuerySection
