import Aeneas
import QueryValidatorGeneratedPrefix
import QueryChunkGeneratedHelper
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume

namespace AspisR1.QueryValidatorChunkArrayBridge

abbrev QueryArray := Array Std.U32 22#usize

theorem index_ok_gen {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize)
    (h : i.val < n.val) : Array.index_usize v i = ok (v.val[i.val]!) := by
  unfold Array.index_usize
  have hl : i.val < v.val.length := by rw [v.property]; exact h
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

theorem generated_chunk0_array_formula
    (queries : QueryArray) (needle : Std.U32) (count : Usize) :
    verifier.query_duplicate_chunk0 queries needle count =
      ok (AspisR1.QueryValidatorGeneratedChunk.formula0 count
        queries.val[0#usize.val]! queries.val[1#usize.val]!
        queries.val[2#usize.val]! queries.val[3#usize.val]!
        queries.val[4#usize.val]! queries.val[5#usize.val]!
        queries.val[6#usize.val]! queries.val[7#usize.val]! needle) := by
  have h0 : Array.index_usize queries 0#usize = ok queries.val[0#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h1 : Array.index_usize queries 1#usize = ok queries.val[1#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h2 : Array.index_usize queries 2#usize = ok queries.val[2#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h3 : Array.index_usize queries 3#usize = ok queries.val[3#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h4 : Array.index_usize queries 4#usize = ok queries.val[4#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h5 : Array.index_usize queries 5#usize = ok queries.val[5#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h6 : Array.index_usize queries 6#usize = ok queries.val[6#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h7 : Array.index_usize queries 7#usize = ok queries.val[7#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have hcopy := AspisR1.QueryValidatorGeneratedChunk.duplicateChunk0_eq_formula
    queries needle count queries.val[0#usize.val]! queries.val[1#usize.val]!
    queries.val[2#usize.val]! queries.val[3#usize.val]!
    queries.val[4#usize.val]! queries.val[5#usize.val]!
    queries.val[6#usize.val]! queries.val[7#usize.val]!
    h0 h1 h2 h3 h4 h5 h6 h7
  change verifier.query_duplicate_chunk0 queries needle count =
      ok (AspisR1.QueryValidatorGeneratedChunk.formula0 count
        queries.val[0#usize.val]! queries.val[1#usize.val]!
        queries.val[2#usize.val]! queries.val[3#usize.val]!
        queries.val[4#usize.val]! queries.val[5#usize.val]!
        queries.val[6#usize.val]! queries.val[7#usize.val]! needle)
  exact hcopy

#print axioms index_ok_gen
#print axioms generated_chunk0_array_formula

end AspisR1.QueryValidatorChunkArrayBridge
