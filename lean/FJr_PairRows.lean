import FJr_InactiveRaw
import FJm_LibraModel
import FJf_ModelPoint
import FJr_CircleLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_PairRows
open Aeneas Aeneas.Std
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev P := FIn_WeightsExtract.circle.SecureCirclePoint
abbrev Alpha := Array AspisR1Stage2.Stage2Finish.K 10#usize

def rows (alpha : Alpha) (p0 p1 : P) (r : Fin 7) : Fin 1024 → FE :=
  let source := FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha
  let point := FJf_ModelPoint.decoded source
  match r.val with
  | 0=>FJr_InactiveRaw.raw
  | 1=>fun j=>algebraMap FK FE (tensorPoint point j)
  | 2=>fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.successorPoint point) j)
  | 3=>fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.xor12Point point) j)
  | 4=>FJm_LibraModel.raw (algebraMap FK FE (FJc_WeightArray.value source 8))
      (algebraMap FK FE (FJc_WeightArray.value source 9))
  | 5=>fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
      (FJc_WeightValues.decode p0.x) (FJc_WeightValues.decode p0.y) j.val)
  | _=>fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
      (FJc_WeightValues.decode p1.x) (FJc_WeightValues.decode p1.y) j.val)

end AspisR1.FJr_PairRows
end
