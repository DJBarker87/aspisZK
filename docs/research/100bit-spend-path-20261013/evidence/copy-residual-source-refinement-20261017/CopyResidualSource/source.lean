import EqualityValueAdapter
import ExtractedMaskHornerStep
import R0P.Copy

/-! Exact generated copy-residual function and row carrier. Source cut only;
pattern/link accumulation and whole evaluate_with_selectors are separate. -/
set_option autoImplicit false
namespace AspisR1CopyResidualCandidate
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

structure pool_v1.pair_forest_copy_terminal.CopyRowExtension where
  producer_values : Array field.QM31 2#usize
  producer_weights : Array field.QM31 2#usize
  consumer_values : Array field.QM31 2#usize
  consumer_weights : Array field.QM31 2#usize

def pool_v1.pair_forest_copy_terminal.copy_residual
  (row : pool_v1.pair_forest_copy_terminal.CopyRowExtension)
  (helper : field.QM31) (chi : field.QM31) :
  Result field.QM31
  := do
  let q ← Array.index_usize row.producer_values 0#usize
  let q1 ← field.QM31.sub chi q
  let q2 ← Array.index_usize row.producer_values 1#usize
  let q3 ← field.QM31.sub chi q2
  let q4 ← Array.index_usize row.consumer_values 0#usize
  let q5 ← field.QM31.sub chi q4
  let q6 ← Array.index_usize row.consumer_values 1#usize
  let q7 ← field.QM31.sub chi q6
  let q8 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 0#usize
  let q9 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 1#usize
  let producer_denominator ← field.QM31.mul q8 q9
  let q10 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 2#usize
  let q11 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 3#usize
  let consumer_denominator ← field.QM31.mul q10 q11
  let q12 ← Array.index_usize row.producer_weights 0#usize
  let q13 ← field.QM31.mul q12 q9
  let q14 ← Array.index_usize row.producer_weights 1#usize
  let q15 ← field.QM31.mul q14 q8
  let producer_numerator ← field.QM31.add q13 q15
  let q16 ← Array.index_usize row.consumer_weights 0#usize
  let q17 ← field.QM31.mul q16 q11
  let q18 ← Array.index_usize row.consumer_weights 1#usize
  let q19 ← field.QM31.mul q18 q10
  let consumer_numerator ← field.QM31.add q17 q19
  let q20 ← field.QM31.mul helper consumer_denominator
  let q21 ← field.QM31.add q20 consumer_numerator
  let q22 ← field.QM31.mul producer_denominator q21
  let q23 ← field.QM31.mul consumer_denominator producer_numerator
  field.QM31.sub q22 q23

end AspisR1CopyResidualCandidate
