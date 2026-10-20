import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkArrayBridgeMore
import QueryChunkGeneratedHelper
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume

namespace AspisR1.QueryValidatorChunkNoHit

abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorGeneratedChunk
open AspisR1.QueryValidatorChunkArrayBridge
open AspisR1.QueryValidatorChunkArrayBridgeMore

theorem usize_index_eq_bang
    (queries : QueryArray) (i : Usize)
    (hi : (↑i : Nat) < (↑queries : List Std.U32).length) :
    queries[i]'hi = queries.val[(↑i : Nat)]! := by
  rw [Aeneas.Std.Array.getElem_Usize_eq queries i hi]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem chunk0_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk0 queries needle count = ok false) :
    (((count > 0#usize) = true → queries[0#usize] ≠ needle) ∧
     ((count > 1#usize) = true → queries[1#usize] ≠ needle) ∧
     ((count > 2#usize) = true → queries[2#usize] ≠ needle) ∧
     ((count > 3#usize) = true → queries[3#usize] ≠ needle) ∧
     ((count > 4#usize) = true → queries[4#usize] ≠ needle) ∧
     ((count > 5#usize) = true → queries[5#usize] ≠ needle) ∧
     ((count > 6#usize) = true → queries[6#usize] ≠ needle) ∧
     ((count > 7#usize) = true → queries[7#usize] ≠ needle)) := by
  have hout := generated_chunk0_array_formula queries needle count
  have hformula : formula0 count
      queries.val[0#usize.val]! queries.val[1#usize.val]!
      queries.val[2#usize.val]! queries.val[3#usize.val]!
      queries.val[4#usize.val]! queries.val[5#usize.val]!
      queries.val[6#usize.val]! queries.val[7#usize.val]! needle = false := by
    have heq := hout.symm.trans hfalse
    injection heq with heq
  have hnot : ¬ (((count > 0#usize) = true ∧ (queries.val[0#usize.val]! = needle) = true) ∨
      ((count > 1#usize) = true ∧ (queries.val[1#usize.val]! = needle) = true) ∨
      ((count > 2#usize) = true ∧ (queries.val[2#usize.val]! = needle) = true) ∨
      ((count > 3#usize) = true ∧ (queries.val[3#usize.val]! = needle) = true) ∨
      ((count > 4#usize) = true ∧ (queries.val[4#usize.val]! = needle) = true) ∨
      ((count > 5#usize) = true ∧ (queries.val[5#usize.val]! = needle) = true) ∨
      ((count > 6#usize) = true ∧ (queries.val[6#usize.val]! = needle) = true) ∨
      ((count > 7#usize) = true ∧ (queries.val[7#usize.val]! = needle) = true)) := by
    intro h
    have ht := (formula0_true_iff count
      queries.val[0#usize.val]! queries.val[1#usize.val]!
      queries.val[2#usize.val]! queries.val[3#usize.val]!
      queries.val[4#usize.val]! queries.val[5#usize.val]!
      queries.val[6#usize.val]! queries.val[7#usize.val]! needle).2 h
    rw [hformula] at ht
    cases ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 0#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inl ⟨hc, by subst needle; simp⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 1#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)
  · intro hc heq
    rw [usize_index_eq_bang queries 2#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))
  · intro hc heq
    rw [usize_index_eq_bang queries 3#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)))
  · intro hc heq
    rw [usize_index_eq_bang queries 4#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))))
  · intro hc heq
    rw [usize_index_eq_bang queries 5#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)))))
  · intro hc heq
    rw [usize_index_eq_bang queries 6#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))))))
  · intro hc heq
    rw [usize_index_eq_bang queries 7#usize (by scalar_tac)] at heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, by subst needle; simp⟩))))))

#print axioms chunk0_nohit

end AspisR1.QueryValidatorChunkNoHit
