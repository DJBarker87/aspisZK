import FJm_KindTwoArithmetic
import FJm_KindTwoTrace
import FJm_VecLens
import FJj_SuccessorDot
import FJj_SuccessorScale
import FJj_LiteralPointTensor
import FJg_ScalarValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_KindTwoMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low
  tensorPoint RoundPairing.dualFold RoundPairing.dot
  FJj_SuccessorHigh.factors FJd_PointReference.pointFactors FJf_ModelPoint.decoded
  R0P.SemSource.successorPoint FIn_WeightsInstall.mapArray

/-- Actual kind2 write. The later Pair continuation and scratch initialization
remain separate obligations; this is not the final-parts part2 theorem. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (hs : FJj_QMSlice.canon (alloc.vec.Vec.deref scratch))
    (run : @FIo_Native.weights.process_kind (FIo_Install.allocation r) (FIo_Install.toWeights w)
      2#usize alpha f 2#usize 64#usize ap0 ap1 scratch before=ok (.Ok (),scratchOut,after)) :
    FIp_ArrayValue.value after 2=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
          (fun j=>algebraMap FK FE (tensorPoint
            (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded
              (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j)))) := by
  rw [FJm_KindTwoArithmetic.value r semAlpha z w hc hw alpha f a0 a1 ap0 ap1 ha0 ha1 hp0 hp1
    scratch scratchOut before after hs run]
  have factors : FJj_SuccessorHigh.factors semAlpha=
      FJd_PointReference.pointFactors (R0P.SemSource.successorPoint
        (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) := by
    unfold FJj_SuccessorHigh.factors
    rfl
  rw [factors]
  exact FJj_LiteralPointTensor.contract (algebraMap FK FE)
    (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha)))
    (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
    (decodeWide (wide a0)) (decodeWide (wide a1))
#print axioms value
end AspisR1.FJm_KindTwoMeaning
end
