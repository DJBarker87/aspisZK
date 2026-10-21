import MultiproofConeSortStep
import Init.Data.List.Sort.Lemmas

set_option autoImplicit false
namespace AspisR1.MultiproofConeSortInsertion
open Aeneas Aeneas.Std Result
open MultiproofSortRef AspisR1.MultiproofConeSortStep

/-- Insertion into a reversed ascending prefix, following the source's
right-to-left comparisons. Equal keys stop immediately. -/
def insertReverse : List U64 → U64 → List U64
  | [], x => [x]
  | y::ys, x => if y ≤ x then x::y::ys else y::insertReverse ys x

theorem insertReverse_perm (xs : List U64) (x : U64) :
    (insertReverse xs x).Perm (x::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertReverse]
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap _ _ _)

theorem insertReverse_sorted (xs : List U64) (x : U64)
    (sorted : xs.Pairwise (fun a b => b ≤ a)) :
    (insertReverse xs x).Pairwise (fun a b => b ≤ a) := by
  induction xs with
  | nil => simp [insertReverse]
  | cons y ys ih =>
    simp only [List.pairwise_cons] at sorted
    simp only [insertReverse]
    split
    next h =>
      simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨h, fun z hz => by have := sorted.1 z hz; scalar_tac⟩, sorted⟩
    next h =>
      refine List.pairwise_cons.mpr ⟨?_, ih sorted.2⟩
      intro z hz
      have mem := (insertReverse_perm ys x).mem_iff.mp hz
      simp only [List.mem_cons] at mem
      rcases mem with rfl | mem
      · scalar_tac
      · exact sorted.1 z mem

/-- Totality, exact insertion content, and unchanged arbitrary scratch suffix.
No sortedness premise is needed for this operational theorem. -/
theorem insert_rows_total (revPrefix : List U64) (x : U64) (suffix : List U64)
    (keys : Array U64 16#usize) (cursor : Usize)
    (shape : keys.val = revPrefix.reverse ++ x::suffix)
    (position : cursor.val = revPrefix.length) :
    ∃ out, sort_reference.insert_rows keys cursor = ok out ∧
      out.val = (insertReverse revPrefix x).reverse ++ suffix := by
  induction revPrefix generalizing keys cursor suffix with
  | nil =>
    have hz : cursor = 0#usize := UScalar.eq_of_val_eq position
    subst cursor
    rw [sort_reference.insert_rows]
    simp only [sort_reference.insert_step, ↓reduceIte, bind_tc_ok]
    exact ⟨keys, rfl, by simpa [insertReverse] using shape⟩
  | cons y ys ih =>
    have length : keys.val.length = 16 := keys.property
    have bound : cursor.val < 16 := by simp [shape, List.length_reverse] at length; simp at position; omega
    have left : keys.val[cursor.val-1]! = y := by
      simp [shape, position, List.reverse_cons, List.append_assoc]
    have right : keys.val[cursor.val]! = x := by
      simp [shape, position, List.reverse_cons, List.append_assoc]
    obtain ⟨step, eqstep, post⟩ := insert_step_total keys cursor bound
    rw [sort_reference.insert_rows, eqstep]
    simp only [bind_tc_ok]
    cases step with
    | Done out =>
      obtain ⟨hout, stop⟩ := post
      subst out
      have le : y ≤ x := by
        rw [left, right] at stop
        rcases stop with zero | le
        · simp at position; omega
        · exact le
      refine ⟨keys, rfl, ?_⟩
      simpa [insertReverse, le, List.reverse_cons, List.append_assoc] using shape
    | Next next lower =>
      obtain ⟨lowerpos, gt, nextdef⟩ := post
      have lp : lower.val = ys.length := by simp at position; omega
      have lc : lower.val = cursor.val-1 := by omega
      have notle : ¬ y ≤ x := by rw [lc, left, right] at gt; scalar_tac
      have nextshape : next.val = ys.reverse ++ x::y::suffix := by
        rw [nextdef]
        simp [Array.set_val_eq, left, right, shape, lp, position,
          List.reverse_cons, List.append_assoc]
      obtain ⟨out, eqout, outshape⟩ := ih (y::suffix) next lower nextshape lp
      refine ⟨out, eqout, ?_⟩
      simpa [insertReverse, notle, List.reverse_cons, List.append_assoc] using outshape

#print axioms insertReverse_perm
#print axioms insertReverse_sorted
#print axioms insert_rows_total
end AspisR1.MultiproofConeSortInsertion
