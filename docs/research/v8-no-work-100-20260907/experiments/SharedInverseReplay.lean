import JoinedInverse

/-! Source-shaped shared inversion with an explicit supplied terminal seed,
not an inverse at each recursive branch. Forward prefixes are the recursive
p arguments; the returns are the reverse source loop. Mutable Vec storage and
machine arithmetic are outside this field/list refinement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 8000
namespace AspisV8.SharedInverseReplay
variable {F : Type*} [Field F] [DecidableEq F]

def backward (p : F) : List F → F → F × List F
  | [], seed => (seed,[])
  | x::xs, seed =>
    let (cursor,out) := backward (p*x) xs seed
    (cursor*x,(p*cursor)::out)

theorem backward_eq_sweep (p : F) (xs : List F) :
    backward p xs (p*xs.prod)⁻¹=JoinedInverse.sweep p xs := by
  induction xs generalizing p with
  | nil => simp only [backward,List.prod_nil,mul_one,JoinedInverse.sweep]
  | cons x xs ih =>
    simp only [backward,List.prod_cons,JoinedInverse.sweep]
    rw [← mul_assoc,ih]

/-- Index zero is stored from the final cursor, exactly as in batch_two;
there is no extra update by xs[0] or inverse hidden in this routine. -/
def finish : List F → F → List F
  | [], _ => []
  | x::xs, seed =>
    let (cursor,out) := backward x xs seed
    cursor::out

theorem finish_correct (xs : List F) : finish xs xs.prod⁻¹=JoinedInverse.core xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [finish,List.prod_cons,backward_eq_sweep,JoinedInverse.core]

/-- The only inverse in the source batch_two execution is (p*q)^-1.
Rejection tests cover both entire input lists before it is evaluated. -/
def batchTwo (xs ys : List F) : Option (List F × List F) :=
  if xs=[] ∨ ys=[] ∨ (0 : F)∈xs ∨ (0 : F)∈ys then none else
    let p := xs.prod
    let q := ys.prod
    let inverse := (p*q)⁻¹
    some (finish xs (inverse*q),finish ys (inverse*p))

theorem batchTwo_eq_separate (xs ys : List F) :
    batchTwo xs ys=JoinedInverse.separate xs ys := by
  by_cases reject : xs=[] ∨ ys=[] ∨ (0 : F)∈xs ∨ (0 : F)∈ys
  · unfold batchTwo JoinedInverse.separate
    rw [if_pos reject,JoinedInverse.checked_correct,JoinedInverse.checked_correct]
    rcases reject with h | h | h | h <;> simp [h]
  · have hx : ∀ x∈xs,x≠0 := by
      intro x member zero
      exact reject (Or.inr (Or.inr (Or.inl (zero ▸ member))))
    have hy : ∀ y∈ys,y≠0 := by
      intro y member zero
      exact reject (Or.inr (Or.inr (Or.inr (zero ▸ member))))
    have seeds := JoinedInverse.shared_product_seeds xs ys hx hy
    have hleft := congrArg Prod.fst seeds
    have hright := congrArg Prod.snd seeds
    simp only [Prod.fst,Prod.snd] at hleft hright
    dsimp only [batchTwo]
    rw [if_neg reject,hleft,hright,finish_correct,finish_correct]
    unfold JoinedInverse.separate JoinedInverse.checked
    rw [if_neg (fun h=>reject (h.elim Or.inl (Or.inr ∘ Or.inr ∘ Or.inl))),
      if_neg (fun h=>reject (h.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr)))]
    rfl

theorem batchTwo_eq_joined (xs ys : List F) :
    batchTwo xs ys=JoinedInverse.joined xs ys := by
  rw [batchTwo_eq_separate,JoinedInverse.joined_eq_separate]

#print axioms backward_eq_sweep
#print axioms finish_correct
#print axioms batchTwo_eq_separate
#print axioms batchTwo_eq_joined
end AspisV8.SharedInverseReplay
