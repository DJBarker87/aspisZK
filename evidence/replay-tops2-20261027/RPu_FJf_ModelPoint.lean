import RPu_FJf_OriginalFactors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_ModelPoint
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)

def decoded (p : Array SQ 10#usize) : Fin 10 → OraclePortCheckpointAbiC5.K :=
  fun i => FJc_WeightArray.value p i.val

theorem tau (d : Fin 5) : FJf_PointIndices.tau d.val=(d18Tau d).val := by
  fin_cases d <;> rfl

theorem factor (p : Array SQ 10#usize) (d : Fin 5) (s : Fin 4) :
    FJf_PointCell.point p d.val s=FJd_PointReference.pointFactors (decoded p) d s := by
  unfold FJf_PointCell.point FJd_PointReference.pointFactors
    FJd_PointReference.coordinateA FJd_PointReference.coordinateB decoded
  rw [tau]

/-- Closed-form tensor VALUE of the factors returned by the actual installed
constructor. This theorem still does not assert execution of Pair's tensor loop. -/
theorem tensor (v : FIn_WeightsExtract.FInVariant) (alpha : Array SQ 10#usize)
    (z : FJf_CircleOuterBody.Z) (w : FIn_WeightsExtract.Weights)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.weights_new v alpha z=ok (.Ok w)) (j : Fin 1024) :
    (∏ d : Fin 5,FJf_FactorArray.value w.factors 0 d.val
      (j.val/4^d.val%4))=tensorPoint (decoded alpha) j := by
  have hf := FJf_OriginalFactors.source v alpha z w hc run
  have he : (∏ d : Fin 5,FJf_FactorArray.value w.factors 0 d.val (j.val/4^d.val%4))=
      FJd_PointReference.tensor (FJd_PointReference.pointFactors (decoded alpha)) j := by
    apply Finset.prod_congr rfl
    intro d _
    exact (hf d ⟨j.val/4^d.val%4,Nat.mod_lt _ (by decide)⟩).trans (factor alpha d _)
  exact he.trans (FJd_PointReference.original (decoded alpha) j)
#print axioms tau
#print axioms factor
#print axioms tensor
end AspisR1.FJf_ModelPoint
end
