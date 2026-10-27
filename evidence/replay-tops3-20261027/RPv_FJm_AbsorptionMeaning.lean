import RPv_FJm_AbsorptionArithmetic
import RPv_FJm_AbsorptionLiteralTensor
import RPv_FJm_AbsorptionTrace
import RPv_FJm_AbsorptionHighReference
import RPv_FJg_ScalarValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (f : Slice U8) (common : Array NQ 16#usize) (partials : Array NE 4#usize)
    (vcom : ∀ j,j<16 → FJf_QMArray.value common j=FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j)
    (vp : FJg_PartialsValue.Values f common partials 4) (cp : FIo_ArrayCanon.Holds partials)
    (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after)) :
    FIp_ArrayValue.value after 3=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
          (fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.xor12Point
            (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j)))) := by
  rw [FJm_AbsorptionArithmetic.value semAlpha z w hc hw f common partials vcom vp cp
    a0 a1 ap0 ap1 ha0 ha1 hp0 hp1 before after run]
  have tensor : (fun j=>algebraMap FK FE (tensorPoint
      (R0P.SemSource.xor12Point (FJf_ModelPoint.decoded
        (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j))=
      FJd_PointReference.tensor (fun d s=>algebraMap FK FE (FJm_AbsorptionScale.factors semAlpha d s)) := by
    funext j
    exact (FJm_AbsorptionLiteralTensor.value semAlpha j).symm
  rw [tensor,RoundPairing.dot]
  simp_rw [FJg_DualTensor.value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms value
end AspisR1.FJm_AbsorptionMeaning
end
