import RPu_FJf_ModelPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_LiteralTensor
open Aeneas Aeneas.Std
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K

def source (p : Array K 10#usize) := FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ p

def factors (p : Array K 10#usize) (d : Fin 5) (s : Fin 4) : FE :=
  algebraMap FK FE (FJf_PointCell.point (source p) d.val s)

/-- Literal SAME constructor semantic alpha and model tensorPoint. -/
theorem value (p : Array K 10#usize) (j : Fin 1024) :
    FJd_PointReference.tensor (factors p) j=
      algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded (source p)) j) := by
  rw [←FJd_PointReference.original (FJf_ModelPoint.decoded (source p)) j]
  unfold FJd_PointReference.tensor factors
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro d _
  rw [FJf_ModelPoint.factor]
#print axioms value
end AspisR1.FJg_LiteralTensor
end
