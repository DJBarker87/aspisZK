import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryValidatorChunkArrayBridgeMore
import QueryChunkGeneratedHelper
import QueryValidatorChunkNoHit
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume

namespace AspisR1.QueryValidatorChunks12NoHit

abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorGeneratedChunk
open AspisR1.QueryValidatorChunkArrayBridgeMore
open AspisR1.QueryValidatorChunkNoHit

theorem chunk1_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk1 queries needle count = ok false) :
    (((count > 0#usize) = true → queries[8#usize] ≠ needle) ∧
     ((count > 1#usize) = true → queries[9#usize] ≠ needle) ∧
     ((count > 2#usize) = true → queries[10#usize] ≠ needle) ∧
     ((count > 3#usize) = true → queries[11#usize] ≠ needle) ∧
     ((count > 4#usize) = true → queries[12#usize] ≠ needle) ∧
     ((count > 5#usize) = true → queries[13#usize] ≠ needle) ∧
     ((count > 6#usize) = true → queries[14#usize] ≠ needle) ∧
     ((count > 7#usize) = true → queries[15#usize] ≠ needle)) := by
  have hout := generated_chunk1_array_formula queries needle count
  have hformula : formula0 count
      queries.val[8#usize.val]! queries.val[9#usize.val]!
      queries.val[10#usize.val]! queries.val[11#usize.val]!
      queries.val[12#usize.val]! queries.val[13#usize.val]!
      queries.val[14#usize.val]! queries.val[15#usize.val]! needle = false := by
    have heq := hout.symm.trans hfalse
    injection heq with heq
  have hnot : ¬ (((count > 0#usize) = true ∧ (queries.val[8#usize.val]! = needle) = true) ∨
      ((count > 1#usize) = true ∧ (queries.val[9#usize.val]! = needle) = true) ∨
      ((count > 2#usize) = true ∧ (queries.val[10#usize.val]! = needle) = true) ∨
      ((count > 3#usize) = true ∧ (queries.val[11#usize.val]! = needle) = true) ∨
      ((count > 4#usize) = true ∧ (queries.val[12#usize.val]! = needle) = true) ∨
      ((count > 5#usize) = true ∧ (queries.val[13#usize.val]! = needle) = true) ∨
      ((count > 6#usize) = true ∧ (queries.val[14#usize.val]! = needle) = true) ∨
      ((count > 7#usize) = true ∧ (queries.val[15#usize.val]! = needle) = true)) := by
    intro h
    have ht := (formula0_true_iff count
      queries.val[8#usize.val]! queries.val[9#usize.val]!
      queries.val[10#usize.val]! queries.val[11#usize.val]!
      queries.val[12#usize.val]! queries.val[13#usize.val]!
      queries.val[14#usize.val]! queries.val[15#usize.val]! needle).2 h
    rw [hformula] at ht
    cases ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 8#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inl ⟨hc, by subst needle; simp⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 9#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)
  · intro hc heq
    rw [usize_index_eq_bang queries 10#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))
  · intro hc heq
    rw [usize_index_eq_bang queries 11#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)))
  · intro hc heq
    rw [usize_index_eq_bang queries 12#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))))
  · intro hc heq
    rw [usize_index_eq_bang queries 13#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)))))
  · intro hc heq
    rw [usize_index_eq_bang queries 14#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))))))
  · intro hc heq
    rw [usize_index_eq_bang queries 15#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, by subst needle; simp⟩))))))

theorem chunk2_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk2 queries needle count = ok false) :
    (((count > 0#usize) = true → queries[16#usize] ≠ needle) ∧
     ((count > 1#usize) = true → queries[17#usize] ≠ needle) ∧
     ((count > 2#usize) = true → queries[18#usize] ≠ needle) ∧
     ((count > 3#usize) = true → queries[19#usize] ≠ needle) ∧
     ((count > 4#usize) = true → queries[20#usize] ≠ needle) ∧
     ((count > 5#usize) = true → queries[21#usize] ≠ needle)) := by
  have hout := generated_chunk2_array_formula queries needle count
  have hformula : formula6 count
      queries.val[16#usize.val]! queries.val[17#usize.val]!
      queries.val[18#usize.val]! queries.val[19#usize.val]!
      queries.val[20#usize.val]! queries.val[21#usize.val]! needle = false := by
    have heq := hout.symm.trans hfalse
    injection heq with heq
  have hnot : ¬ (((count > 0#usize) = true ∧ (queries.val[16#usize.val]! = needle) = true) ∨
      ((count > 1#usize) = true ∧ (queries.val[17#usize.val]! = needle) = true) ∨
      ((count > 2#usize) = true ∧ (queries.val[18#usize.val]! = needle) = true) ∨
      ((count > 3#usize) = true ∧ (queries.val[19#usize.val]! = needle) = true) ∨
      ((count > 4#usize) = true ∧ (queries.val[20#usize.val]! = needle) = true) ∨
      ((count > 5#usize) = true ∧ (queries.val[21#usize.val]! = needle) = true)) := by
    intro h
    have ht := (formula6_true_iff count
      queries.val[16#usize.val]! queries.val[17#usize.val]!
      queries.val[18#usize.val]! queries.val[19#usize.val]!
      queries.val[20#usize.val]! queries.val[21#usize.val]! needle).2 h
    rw [hformula] at ht
    cases ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 16#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inl ⟨hc, by subst needle; simp⟩
  · intro hc heq
    rw [usize_index_eq_bang queries 17#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)
  · intro hc heq
    rw [usize_index_eq_bang queries 18#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))
  · intro hc heq
    rw [usize_index_eq_bang queries 19#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩)))
  · intro hc heq
    rw [usize_index_eq_bang queries 20#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by subst needle; simp⟩))))
  · intro hc heq
    rw [usize_index_eq_bang queries 21#usize (by scalar_tac)] at heq
    apply hnot; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, by subst needle; simp⟩))))

#print axioms chunk1_nohit
#print axioms chunk2_nohit

end AspisR1.QueryValidatorChunks12NoHit
