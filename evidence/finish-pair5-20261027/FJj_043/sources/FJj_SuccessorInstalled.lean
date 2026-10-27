import FJj_SuccessorFactors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorInstalled
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem value (v : transport.Variant) (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w)) :
    (∀ row,w.factors.val[1]?=some row → FJf_FactorArray.rowCanon row) ∧
    ∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value w.factors 1 d.val s.val=
      FJd_PointReference.pointFactors
        (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded
          (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) d s :=
  FJj_SuccessorFactors.source _ _ _ w hc (FJc_Constructor.source v alpha z w run)
#print axioms value
end AspisR1.FJj_SuccessorInstalled
end
