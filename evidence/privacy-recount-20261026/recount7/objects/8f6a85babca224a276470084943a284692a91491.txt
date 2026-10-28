import PV_B3_EvalRank222
import PV_B3_BoundedLoop
namespace PV_B3_EvalFinite222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Copy_222 PV_B3_EvalCounter222
set_option autoImplicit false

def body (column : Slice Q) (weights : host_multilinear.SparseWeights) (s : State) :
    Result (ControlFlow State Q) :=
  host_multilinear.multilinear_evaluate_qm31_loop.body column weights s.1 s.2

theorem decreases (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (s next : State) (h : body column weights s = ok (cont next)) :
    PV_B3_EvalRank222.rank weights next < PV_B3_EvalRank222.rank weights s := by
  rcases s with ⟨sum, i⟩
  exact PV_B3_EvalRank222.decreases column weights sum i next h

theorem source (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (sum : Q) (i : Usize) :
    host_multilinear.multilinear_evaluate_qm31_loop column weights sum i =
      PV_B3_BoundedLoop.bounded (body column weights)
        (PV_B3_EvalRank222.rank weights (sum, i)) (sum, i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body column weights)
    (PV_B3_EvalRank222.rank weights) (decreases column weights) _ _ (Nat.le_refl _)

#print axioms body
#print axioms decreases
#print axioms source
end PV_B3_EvalFinite222
