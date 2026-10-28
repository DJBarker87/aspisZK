import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_PublicationIndices

def seek (x : Nat) : List Nat → Nat
  | [] => 0
  | y::ys => if y<x then 1+seek x ys else 0

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y::ys => if y<x then y::insert x ys else if y=x then y::ys else x::y::ys

/-- The native Vec guard checks at==len first, so a missing getElem? is
exactly the unconditional insertion-at-end case. -/
def sourceInsert (x : Nat) (xs : List Nat) : List Nat :=
  let pos :=  seek x xs
  if xs[pos]? = some x then xs else xs.insertIdx pos x

theorem seek_bound (x : Nat) (xs : List Nat) : seek x xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases h : y<x <;> simp [seek,h] <;> omega
#print axioms seek_bound

theorem source_insert (x : Nat) (xs : List Nat) : sourceInsert x xs = insert x xs := by
  induction xs with
  | nil => simp [sourceInsert,seek,insert]
  | cons y ys ih =>
    by_cases h : y<x
    · simp only [sourceInsert,seek,h,ite_true]
      rw [Nat.add_comm 1 (seek x ys),List.getElem?_cons_succ,List.insertIdx_succ_cons]
      rw [insert,if_pos h,← ih]
      simp only [sourceInsert]
      split_ifs <;> rfl
    · by_cases he : y=x
      · simp [sourceInsert,seek,insert,h,he]
      · simp [sourceInsert,seek,insert,h,he,Ne.symm he]
#print axioms source_insert

theorem insert_length (x : Nat) (xs : List Nat) : (insert x xs).length≤xs.length+1 := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    by_cases h : y<x
    · simp [insert,h];omega
    · by_cases he : y=x <;> simp [insert,h,he]
#print axioms insert_length

theorem insert_mem (x z : Nat) (xs : List Nat) : z ∈ insert x xs ↔ z=x ∨ z∈xs := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    by_cases h : y<x
    · simp [insert,h,ih,or_left_comm,or_comm]
    · by_cases he : y=x <;> simp [insert,h,he,or_left_comm,or_comm]
#print axioms insert_mem

theorem insert_ordered (x : Nat) (xs : List Nat) (h : xs.Pairwise (· < ·)) :
    (insert x xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp h
    by_cases hy : y<x
    · rw [insert,if_pos hy]
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        rcases (insert_mem x z ys).mp hz with rfl | hz
        · exact hy
        · exact head z hz
      · exact ih tail
    · rw [insert,if_neg hy]
      by_cases he : y=x
      · rw [if_pos he];exact h
      · rw [if_neg he]
        apply List.pairwise_cons.mpr
        constructor
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · omega
          · have hlt:=head z hz;omega
        · exact h
#print axioms insert_ordered

def build : List Nat → List Nat → List Nat
  | out, [] => out
  | out, x::xs => build (insert x out) xs

theorem build_length (out xs : List Nat) : (build out xs).length≤out.length+xs.length := by
  induction xs generalizing out with
  | nil => simp [build]
  | cons x xs ih =>
    have hi := insert_length x out
    have ht := ih (insert x out)
    simp only [build,List.length_cons]
    omega
#print axioms build_length

theorem build_ordered (out xs : List Nat) (h : out.Pairwise (· < ·)) :
    (build out xs).Pairwise (· < ·) := by
  induction xs generalizing out with
  | nil => exact h
  | cons x xs ih => exact ih (insert x out) (insert_ordered x out h)
#print axioms build_ordered

theorem build_mem (out xs : List Nat) (z : Nat) :
    z∈build out xs ↔ z∈out ∨ z∈xs := by
  induction xs generalizing out with
  | nil => simp [build]
  | cons x xs ih => simp [build,ih,insert_mem,or_assoc,or_left_comm,or_comm]
#print axioms build_mem

/-- Native publication uses these two batches of the same ordered 22-query
array, optionally dividing each index by four before insertion. -/
def publication (queries : List Nat) (begin_ end_ : Nat) (folded : Bool) : List Nat :=
  build [] (((queries.drop begin_).take (end_-begin_)).map
    (fun q => if folded then q/4 else q))

theorem publication_length (queries : List Nat) (begin_ end_ : Nat) (folded : Bool) :
    (publication queries begin_ end_ folded).length≤end_-begin_ := by
  have h:=build_length [] (((queries.drop begin_).take (end_-begin_)).map
    (fun q => if folded then q/4 else q))
  simp only [List.length_nil,zero_add,List.length_map,List.length_take] at h
  exact h.trans (Nat.min_le_left _ _)
#print axioms publication_length

theorem publication_ordered (queries : List Nat) (begin_ end_ : Nat) (folded : Bool) :
    (publication queries begin_ end_ folded).Pairwise (· < ·) := by
  exact build_ordered [] _ (by simp)
#print axioms publication_ordered
end PV_L2D_PublicationIndices
