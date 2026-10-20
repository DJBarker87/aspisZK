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

theorem chunk0_nohit
    (queries : QueryArray) (needle : Std.U32) (count : Usize)
    (hfalse : verifier.query_duplicate_chunk0 queries needle count = ok false) :
    (((count > 0#usize) = true → queries.val[0#usize.val]! ≠ needle) ∧
     ((count > 1#usize) = true → queries.val[1#usize.val]! ≠ needle) ∧
     ((count > 2#usize) = true → queries.val[2#usize.val]! ≠ needle) ∧
     ((count > 3#usize) = true → queries.val[3#usize.val]! ≠ needle) ∧
     ((count > 4#usize) = true → queries.val[4#usize.val]! ≠ needle) ∧
     ((count > 5#usize) = true → queries.val[5#usize.val]! ≠ needle) ∧
     ((count > 6#usize) = true → queries.val[6#usize.val]! ≠ needle) ∧
     ((count > 7#usize) = true → queries.val[7#usize.val]! ≠ needle)) := by
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
    apply hnot
    exact Or.inl ⟨hc, by simp [heq]⟩
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inl ⟨hc, by simp [heq]⟩)
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inl ⟨hc, by simp [heq]⟩))
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by simp [heq]⟩)))
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by simp [heq]⟩))))
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by simp [heq]⟩)))))
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, by simp [heq]⟩))))))
  · intro hc heq
    apply hnot
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, by simp [heq]⟩))))))

#print axioms chunk0_nohit

end AspisR1.QueryValidatorChunkNoHit
