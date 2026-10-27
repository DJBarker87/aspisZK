import RPu_FJj_SuccessorTensor
import RPu_FJj_ByteDotFinal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorDot
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 1#usize=ok row)
    (input scratch : Slice NQ) (hs : FJj_QMSlice.canon input)
    (tensor : FIo_Native.weights.Weights.tensor (FIo_Install.toWeights w) 1#usize 2#usize input=ok scratch)
    (f : Slice U8) (dot dotOut : FIo_Native.fast_pairing.EbyKDot) (result : NE)
    (new : FIo_Native.fast_pairing.EbyKDot.new=ok dot)
    (run : FIo_Native.weights.push_byte_products dot f scratch 64#usize=ok (.Ok (),dotOut))
    (finish : FIo_Native.fast_pairing.EbyKDot.finish dotOut=ok result) :
    FIo_WideValues.Canon result ∧ decodeWide (wide result)=∑ i : Fin 64,
      FJc_InactiveCoefficientsModel.field f i.val*
        FJg_TensorProduct.high (fun d s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
          (FJj_SuccessorHigh.factors alpha d s)) i := by
  have tensorValue := FJj_SuccessorTensor.value alpha z w hc hw row hr input scratch hs tensor
  have dotValue := FJj_ByteDotFinal.value f scratch tensorValue.1 dot dotOut result new run finish
  refine ⟨dotValue.1,?_⟩
  rw [dotValue.2]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorValue.2.2 i]
#print axioms value
end AspisR1.FJj_SuccessorDot
end
