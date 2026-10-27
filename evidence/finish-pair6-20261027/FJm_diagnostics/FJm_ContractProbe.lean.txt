import FJj_LiteralPointTensor
import FJj_SuccessorHigh
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_ContractProbe
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low
  tensorPoint RoundPairing.dualFold RoundPairing.dot
  FJd_PointReference.pointFactors
set_option pp.explicit true in
#check @FJj_LiteralPointTensor.contract

theorem value (p : Fin 10 → FK) (f : Fin 64 → FE) (a0 a1 : FE) :
    FJg_DualTensor.low (fun s=>algebraMap FK FE (FJd_PointReference.pointFactors p 0 s)) a0 *
      FJg_DualTensor.low (fun s=>algebraMap FK FE (FJd_PointReference.pointFactors p 1 s)) a1 *
      (∑ i : Fin 64,f i*FJg_TensorProduct.high (fun d s=>algebraMap FK FE (FJd_PointReference.pointFactors p d s)) i)=
    RoundPairing.dot f (RoundPairing.dualFold (n:=64) a1
      (RoundPairing.dualFold (n:=256) a0 (fun j=>algebraMap FK FE (tensorPoint p j)))) := by
  exact FJj_LiteralPointTensor.contract (algebraMap FK FE) p f a0 a1
#print axioms value
end AspisR1.FJm_ContractProbe
end
