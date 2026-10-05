import AspisV8R19.R833RootFixedJointPolynomial
import AspisV8R19.R825CompleteSourceDeterminant
import AspisV8R19.R779FixedPoint1LowKernel
import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R15.ExactTowerBase

set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R835RootFixedJointPolynomialNonzero
open MvPolynomial
open AspisV8R15.ExactTowerBase
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R791QM31JointNormalization
open AspisV8R19.R745JointObservationPolynomial
open AspisV8R19.R833RootFixedJointPolynomial
noncomputable section
local instance : Fact (1 < 2147483647) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2147483647) := m31PrimeFact
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

theorem root_fixed_det_nonzero (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    (rootFixedMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) t ht noneOne).det ≠ 0 := by
  intro hdet
  let alpha : QM31Exact := witnessEmbedding (7 : M)
  let u : QM31Exact := witnessEmbedding (2 : M)
  let v : QM31Exact := witnessEmbedding (3 : M)
  let kappa : QM31Exact := witnessEmbedding (5 : M)
  let tau : QM31Exact := 0
  let zz : Fin 10 → QM31Exact := fun i => witnessEmbedding (z i)
  have heval :
      eval (assignment alpha u v kappa tau zz)
        (rootFixedMatrix (witnessEmbedding half)
          (witnessEmbedding (536870912 : M)) t ht noneOne).det = 0 := by
    have h := congrArg (eval (assignment alpha u v kappa tau zz)) hdet
    simpa only [map_zero] using h
  rw [eval_rootFixedMatrix_det
      (witnessEmbedding half) (witnessEmbedding (536870912 : M))
      alpha u v kappa tau zz t ht noneOne] at heval
  have hnormalized :=
    AspisV8R19.R825CompleteSourceDeterminant.normalized_qm31_det_ne_zero t ht noneOne
  exact hnormalized heval

#print axioms root_fixed_det_nonzero
end
end AspisV8R19.R835RootFixedJointPolynomialNonzero
