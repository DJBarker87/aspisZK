import Mathlib.Tactic
namespace AspisV8.JoinedInverse
variable {F : Type*} [Field F] [DecidableEq F]

-- Forward prefix construction followed by source-shaped backward updates.
-- p is the already accumulated prefix; only the empty suffix takes an inverse.
def sweep (p : F) : List F → F × List F
  | [] => (p⁻¹, [])
  | x::xs =>
    let (i,ys) := sweep (p*x) xs
    (i*x, (p*i)::ys)

theorem backward_step (p x : F) (hp : p≠0) (hx : x≠0) :
    ((p*x)⁻¹*x, p*(p*x)⁻¹) = (p⁻¹,x⁻¹) := by
  ext <;> field_simp

theorem sweep_correct (xs : List F) (p : F) (hp : p≠0)
    (hz : ∀ x∈xs, x≠0) :
    sweep p xs = (p⁻¹, xs.map (fun x => x⁻¹)) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    have hx : x≠0 := hz x (by simp)
    have ht : ∀ y∈xs, y≠0 := fun y hy => hz y (by simp [hy])
    simp only [sweep,ih (p*x) (mul_ne_zero hp hx) ht,List.map_cons]
    have h := backward_step p x hp hx
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst,Prod.snd] at h1 h2
    rw [h1,h2]

def core : List F → List F
  | [] => []
  | x::xs => let (i,ys) := sweep x xs; i::ys

theorem core_correct (xs : List F) (hz : ∀ x∈xs, x≠0) :
    core xs = xs.map (fun x => x⁻¹) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have hx : x≠0 := hz x (by simp)
    have ht : ∀ y∈xs, y≠0 := fun y hy => hz y (by simp [hy])
    simp [core,sweep_correct xs x hx ht]

def checked (xs : List F) : Option (List F) :=
  if xs=[] ∨ 0∈xs then none else some (core xs)

theorem checked_correct (xs : List F) :
    checked xs = if xs=[] ∨ 0∈xs then none
      else some (xs.map (fun x => x⁻¹)) := by
  unfold checked
  split
  · rfl
  · rename_i h
    rw [core_correct xs (by intro x hx hx0; subst x; exact h (Or.inr hx))]

def separate (xs ys : List F) : Option (List F × List F) := do
  let a ← checked xs
  let b ← checked ys
  pure (a,b)

def joined (xs ys : List F) : Option (List F × List F) :=
  if xs=[] ∨ ys=[] then none else
    (checked (xs++ys)).map (fun all => (all.take xs.length, all.drop xs.length))

theorem joined_eq_separate (xs ys : List F) :
    joined xs ys = separate xs ys := by
  rw [joined,separate,checked_correct,checked_correct,checked_correct]
  by_cases hx : xs=[] <;> by_cases hy : ys=[] <;>
    by_cases hzx : (0:F)∈xs <;> by_cases hzy : (0:F)∈ys <;>
    simp_all [List.map_append]

theorem concat_zero_iff (xs ys : List F) :
    (0:F) ∈ xs++ys ↔ 0∈xs ∨ 0∈ys := List.mem_append

-- Source-sized costs for the retained 3(n-1) prefix/backward implementation.
theorem extra_products : 3*(132-1) = 3*(88-1)+3*(44-1)+3 := by norm_num
theorem first_fold_index (i : Nat) (hi : i<22) :
    88+2*i<132 ∧ 88+2*i+1<132 := by omega

-- Alternate memory layout: retain separate prefixes, share only one inverse
-- of their final product, then seed the two unchanged backward passes.
theorem shared_seeds (p q : F) (hp : p≠0) (hq : q≠0) :
    ((p*q)⁻¹*q,(p*q)⁻¹*p) = (p⁻¹,q⁻¹) := by
  have h := backward_step p q hp hq
  simpa only [mul_comm] using h

theorem products_nonzero (xs : List F) (hz : ∀ x∈xs,x≠0) :
    xs.prod≠0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons]
    exact mul_ne_zero (hz x (by simp))
      (ih (fun y hy => hz y (by simp [hy])))

theorem shared_product_seeds (xs ys : List F)
    (hx : ∀ x∈xs,x≠0) (hy : ∀ y∈ys,y≠0) :
    ((xs.prod*ys.prod)⁻¹*ys.prod,(xs.prod*ys.prod)⁻¹*xs.prod) =
      (xs.prod⁻¹,ys.prod⁻¹) :=
  shared_seeds _ _ (products_nonzero xs hx) (products_nonzero ys hy)

#print axioms backward_step
#print axioms sweep_correct
#print axioms core_correct
#print axioms checked_correct
#print axioms joined_eq_separate
#print axioms concat_zero_iff
#print axioms extra_products
#print axioms first_fold_index
#print axioms shared_seeds
#print axioms products_nonzero
#print axioms shared_product_seeds
end AspisV8.JoinedInverse
