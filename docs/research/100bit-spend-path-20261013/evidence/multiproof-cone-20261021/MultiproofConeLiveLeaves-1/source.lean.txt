import MultiproofConeLiveOrder

set_option autoImplicit false
namespace AspisR1.MultiproofConeLiveLeaves
open MultiproofConeLiveOrder

/-- Index projection of leaf_insert. Duplicate digest disagreement rejects
before any index mutation; it therefore cannot invalidate this success law. -/
def insert (k : Nat → Nat) (d x : Nat) : (Nat → Nat) × Nat :=
  if 0<d ∧ k (d-1)=x then (k,d)
  else (fun j => if j=d then x else k j,d+1)

theorem insert_sorted (k : Nat → Nat) (d x : Nat) (sorted : Strict k 0 d)
    (bound : ∀ a, a<d → k a≤x) : Strict (insert k d x).1 0 (insert k d x).2 := by
  unfold insert
  split
  next => exact sorted
  next different =>
    intro a b _ ab bd
    by_cases be : b=d
    · subst b
      have ae : a≠d := by omega
      simp only [if_neg ae,↓reduceIte]
      have lastBound := bound (d-1) (by omega)
      have lastNe : k (d-1)≠x := by intro eq;exact different ⟨by omega,eq⟩
      by_cases last : a=d-1
      · rw [last];omega
      · have lt := sorted a (d-1) (by omega) (by omega) (by omega)
        omega
    · have ae : a≠d := by omega
      simp only [if_neg ae,if_neg be]
      exact sorted a b (by omega) ab (by omega)

theorem insert_upper (k : Nat → Nat) (d x y : Nat)
    (bound : ∀ a, a<d → k a≤y) (xy : x≤y) :
    ∀ a, a<(insert k d x).2 → (insert k d x).1 a≤y := by
  unfold insert
  split
  next => exact bound
  next =>
    intro a ad
    by_cases ae : a=d
    · simp only [ae,↓reduceIte];exact xy
    · simp only [if_neg ae];exact bound a (by omega)

def build : List Nat → (Nat → Nat) → Nat → (Nat → Nat) × Nat
  | [],k,d => (k,d)
  | x::xs,k,d => let next := insert k d x; build xs next.1 next.2

/-- Complete leaf index induction on an ascending packed-index stream.
Ties are allowed in the input; the successful output is strictly ascending. -/
theorem build_sorted (xs : List Nat) (k : Nat → Nat) (d : Nat)
    (ordered : xs.Pairwise (·≤·)) (sorted : Strict k 0 d)
    (future : ∀ a, a<d → ∀ x∈xs, k a≤x) :
    Strict (build xs k d).1 0 (build xs k d).2 := by
  induction xs generalizing k d with
  | nil => exact sorted
  | cons x xs ih =>
    obtain ⟨xBound,tailSorted⟩ := List.pairwise_cons.mp ordered
    exact ih (insert k d x).1 (insert k d x).2 tailSorted
      (insert_sorted k d x sorted (fun a ha => future a ha x (by simp)))
      (fun a ha y hy => insert_upper k d x y
        (fun b hb => future b hb y (by simp [hy])) (xBound y hy) a ha)

theorem empty_build_sorted (xs : List Nat) (scratch : Nat → Nat)
    (ordered : xs.Pairwise (·≤·)) :
    Strict (build xs scratch 0).1 0 (build xs scratch 0).2 := by
  exact build_sorted xs scratch 0 ordered (by simp [Strict]) (by simp)

/-- The sorted leaf output supplies every level's initial invariant, including
height 18, independently of all digest values and supplied sibling bytes. -/
theorem batch_levels_sorted (xs : List Nat) (scratch out : Nat → Nat) (height m : Nat)
    (ordered : xs.Pairwise (·≤·))
    (run : Levels height (build xs scratch 0).1 (build xs scratch 0).2 out m) :
    Strict out 0 m :=
  all_levels height _ _ out m run (empty_build_sorted xs scratch ordered)

#print axioms insert_sorted
#print axioms insert_upper
#print axioms build_sorted
#print axioms empty_build_sorted
#print axioms batch_levels_sorted
end AspisR1.MultiproofConeLiveLeaves
