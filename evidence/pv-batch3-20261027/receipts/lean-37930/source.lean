import PV_B3_PrefixFinite222
import PV_B3_SuffixFinite222
import PV_B3_WeightFinite222
import PV_B3_WeightsFinite222
import PV_B3_EvalFinite222
namespace PV_B3_MultilinearFinite222
open Aeneas Aeneas.Std Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

-- Finite reference for the emitted copy. The inner weight loop has its own
-- universal factorization in PV_B3_WeightFinite222.source.
def sparse (point : Array Q 10#usize) : Result host_multilinear.SparseWeights := do
  let prefix_len ← PV_B3_BoundedLoop.bounded
    (host_multilinear.sparse_eq_weights_loop0.body point) 10 10#usize
  let trailing_boolean ← lift (Usize.wrapping_sub 10#usize prefix_len)
  let suffix ← PV_B3_BoundedLoop.bounded (PV_B3_SuffixFinite222.body point)
    (10-prefix_len.val) (0#usize,prefix_len)
  let a := Array.repeat 1024#usize (0#usize,aspis_core.field.QM31.ZERO)
  let bound ← lift (Usize.wrapping_shl 1#usize (UScalar.cast .U32 prefix_len))
  let data ← PV_B3_BoundedLoop.bounded
    (PV_B3_WeightsFinite222.body point prefix_len trailing_boolean suffix bound)
    bound.val (a,0#usize)
  ok {data := data, len := bound}

theorem sparse_source (point : Array Q 10#usize) :
    host_multilinear.sparse_eq_weights point = sparse point := by
  unfold host_multilinear.sparse_eq_weights sparse
  simp_rw [PV_B3_PrefixFinite222.source, PV_B3_SuffixFinite222.source,
    PV_B3_WeightsFinite222.source]
  rfl

def evaluate (column : Slice Q) (point : Array Q 10#usize) : Result (Option Q) := do
  if Slice.len column != 1024#usize then ok none
  else
    let weights ← sparse point
    let sum ← PV_B3_BoundedLoop.bounded (PV_B3_EvalFinite222.body column weights)
      weights.len.val (aspis_core.field.QM31.ZERO,0#usize)
    ok (some sum)

theorem source (column : Slice Q) (point : Array Q 10#usize) :
    host_multilinear.multilinear_evaluate_qm31 column point = evaluate column point := by
  unfold host_multilinear.multilinear_evaluate_qm31 evaluate
  simp_rw [sparse_source, PV_B3_EvalFinite222.source]
  rfl

#print axioms sparse
#print axioms sparse_source
#print axioms evaluate
#print axioms source
end PV_B3_MultilinearFinite222
