import FJg_DualTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_LiteralPointTensor
open scoped BigOperators
variable {K E : Type} [Field K] [Field E]

theorem tensor (φ : K →+* E) (p : Fin 10 → K) (j : Fin 1024) :
    FJd_PointReference.tensor (fun d s=>φ (FJd_PointReference.pointFactors p d s)) j=
      φ (tensorPoint p j) := by
  rw [←FJd_PointReference.original p j]
  unfold FJd_PointReference.tensor
  rw [map_prod]

theorem contract (φ : K →+* E) (p : Fin 10 → K) (f : Fin 64 → E) (a0 a1 : E) :
    FJg_DualTensor.low (fun s=>φ (FJd_PointReference.pointFactors p 0 s)) a0*
      FJg_DualTensor.low (fun s=>φ (FJd_PointReference.pointFactors p 1 s)) a1*
      (∑ i : Fin 64,f i*FJg_TensorProduct.high (fun d s=>φ (FJd_PointReference.pointFactors p d s)) i)=
      RoundPairing.dot f (RoundPairing.dualFold (n:=64) a1
        (RoundPairing.dualFold (n:=256) a0 (fun j=>φ (tensorPoint p j)))) := by
  have eq : (fun j=>φ (tensorPoint p j))=
      FJd_PointReference.tensor (fun d s=>φ (FJd_PointReference.pointFactors p d s)) := by
    funext j
    exact (tensor φ p j).symm
  rw [eq,RoundPairing.dot]
  simp_rw [FJg_DualTensor.value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms tensor
#print axioms contract
end AspisR1.FJj_LiteralPointTensor
end
