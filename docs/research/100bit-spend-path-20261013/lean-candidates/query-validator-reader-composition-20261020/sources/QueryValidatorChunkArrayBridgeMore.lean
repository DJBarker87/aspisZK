import Aeneas
import QueryValidatorGeneratedPrefix
import QueryValidatorChunkArrayBridge
import QueryChunkGeneratedHelper
import Aeneas.Tactic.Solver.ScalarTac
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume

namespace AspisR1.QueryValidatorChunkArrayBridgeMore

abbrev QueryArray := Array Std.U32 22#usize

open AspisR1.QueryValidatorChunkArrayBridge
open AspisR1.QueryValidatorGeneratedChunk

theorem generated_chunk1_array_formula
    (queries : QueryArray) (needle : Std.U32) (count : Usize) :
    verifier.query_duplicate_chunk1 queries needle count =
      ok (formula0 count
        queries.val[8#usize.val]! queries.val[9#usize.val]!
        queries.val[10#usize.val]! queries.val[11#usize.val]!
        queries.val[12#usize.val]! queries.val[13#usize.val]!
        queries.val[14#usize.val]! queries.val[15#usize.val]! needle) := by
  have h8 : Array.index_usize queries 8#usize = ok queries.val[8#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h9 : Array.index_usize queries 9#usize = ok queries.val[9#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h10 : Array.index_usize queries 10#usize = ok queries.val[10#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h11 : Array.index_usize queries 11#usize = ok queries.val[11#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h12 : Array.index_usize queries 12#usize = ok queries.val[12#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h13 : Array.index_usize queries 13#usize = ok queries.val[13#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h14 : Array.index_usize queries 14#usize = ok queries.val[14#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h15 : Array.index_usize queries 15#usize = ok queries.val[15#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  unfold verifier.query_duplicate_chunk1
  simp only [h8, h9, h10, h11, h12, h13, h14, h15, bind_tc_ok]
  rfl

def formula6 (count : Usize) (x0 x1 x2 x3 x4 x5 needle : Std.U32) : Bool :=
  ((((((((count > 0#usize) && (x0 = needle)) || ((count > 1#usize) && (x1 = needle))) ||
    ((count > 2#usize) && (x2 = needle))) || ((count > 3#usize) && (x3 = needle))) ||
    ((count > 4#usize) && (x4 = needle))) || ((count > 5#usize) && (x5 = needle))))

theorem formula6_true_iff (count : Usize) (x0 x1 x2 x3 x4 x5 needle : Std.U32) :
    formula6 count x0 x1 x2 x3 x4 x5 needle = true ↔
      (((count > 0#usize) = true ∧ (x0 = needle) = true) ∨
       ((count > 1#usize) = true ∧ (x1 = needle) = true) ∨
       ((count > 2#usize) = true ∧ (x2 = needle) = true) ∨
       ((count > 3#usize) = true ∧ (x3 = needle) = true) ∨
       ((count > 4#usize) = true ∧ (x4 = needle) = true) ∨
       ((count > 5#usize) = true ∧ (x5 = needle) = true)) := by
  simp [formula6, or_assoc]

theorem generated_chunk2_array_formula
    (queries : QueryArray) (needle : Std.U32) (count : Usize) :
    verifier.query_duplicate_chunk2 queries needle count =
      ok (formula6 count
        queries.val[16#usize.val]! queries.val[17#usize.val]!
        queries.val[18#usize.val]! queries.val[19#usize.val]!
        queries.val[20#usize.val]! queries.val[21#usize.val]! needle) := by
  have h16 : Array.index_usize queries 16#usize = ok queries.val[16#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h17 : Array.index_usize queries 17#usize = ok queries.val[17#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h18 : Array.index_usize queries 18#usize = ok queries.val[18#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h19 : Array.index_usize queries 19#usize = ok queries.val[19#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h20 : Array.index_usize queries 20#usize = ok queries.val[20#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  have h21 : Array.index_usize queries 21#usize = ok queries.val[21#usize.val]! :=
    index_ok_gen queries _ (by scalar_tac)
  unfold verifier.query_duplicate_chunk2
  simp only [h16, h17, h18, h19, h20, h21, bind_tc_ok]
  rfl

#print axioms generated_chunk1_array_formula
#print axioms formula6_true_iff
#print axioms generated_chunk2_array_formula

end AspisR1.QueryValidatorChunkArrayBridgeMore
