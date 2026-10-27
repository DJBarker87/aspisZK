import RPv_FJj_TensorTwo
import RPv_FJj_SuccessorRow
import RPv_FJj_SuccessorHigh
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorTensor
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 1#usize=ok row)
    (input out : Slice NQ) (hs : FJj_QMSlice.canon input)
    (run : FIo_Native.weights.Weights.tensor (FIo_Install.toWeights w) 1#usize 2#usize input=ok out) :
    FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧ ∀ i : Fin 64,
      algebraMap FK FE (FJj_QMSlice.value out i.val)=
        FJg_TensorProduct.high (fun d s=>algebraMap FK FE (FJj_SuccessorHigh.factors alpha d s)) i := by
  have cr := FJj_SuccessorRow.value alpha z w hc hw row hr
  obtain ⟨co,len,values⟩ := FJj_TensorTwo.value (FIo_Install.toWeights w) 1#usize row hr cr input out hs run
  refine ⟨co,len,?_⟩
  intro i
  rw [values i.val i.isLt,FJj_SuccessorHigh.value alpha z w hc hw row hr i]
  exact FJj_HighProductInstances.map (algebraMap FK FE) (FJj_SuccessorHigh.factors alpha) i
#print axioms value
end AspisR1.FJj_SuccessorTensor
end
