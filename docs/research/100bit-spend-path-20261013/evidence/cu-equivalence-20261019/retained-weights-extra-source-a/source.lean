import CuSavingsRetainedCompositionTx1Source
open Aeneas Aeneas.Std Result
namespace AspisR1RhoPowerTail
/-- [aspis_r1_cu_canonical_dots::extra]:
    Source: 'lib.rs', lines 3:0-3:75
    Visibility: public -/
def retained.weights_extra
  (alpha : Array aspis_core.field.QM31 10#usize) : Result (Array aspis_core.field.QM31 2#usize) := do
  let q ← Array.index_usize alpha 8#usize
  let q1 ← Array.index_usize alpha 9#usize
  ok (Array.make 2#usize [ q, q1 ])

#print axioms retained.weights_extra
end AspisR1RhoPowerTail
