import QuadraticParityCharacteristic
import Mathlib.RingTheory.Localization.FractionRing

/-! Return the characteristic-aware fraction-field resultant to the
literal polynomial coefficient ring. Localized squarefreeness is explicit
and is supplied by the separate parity-localization construction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.QuadraticResultantDescent
noncomputable section
open Polynomial

theorem fixed_resultant_nonzero
    {K : Type*} [Field K] (p : Nat) [CharP K p]
    (R : Polynomial K[X])
    (positive : 0 < R.natDegree) (small : R.natDegree < p)
    (squarefree : Squarefree
      (R.map (algebraMap K[X] (FractionRing K[X])))) :
    R.resultant R.derivative R.natDegree (R.natDegree-1) ≠ 0 := by
  let phi : K[X] →+* FractionRing K[X] := algebraMap K[X] (FractionRing K[X])
  have injective : Function.Injective phi := IsFractionRing.injective _ _
  have degree : (R.map phi).natDegree = R.natDegree :=
    Polynomial.natDegree_map_eq_of_injective injective R
  have fieldResult := QuadraticParityCharacteristic.fixed_resultant_nonzero_of_squarefree_small
    p (R.map phi) (by rwa [degree]) (by rwa [degree]) squarefree
  rw [degree, Polynomial.derivative_map] at fieldResult
  intro zero
  apply fieldResult
  rw [Polynomial.resultant_map_map, zero, map_zero]

#print axioms fixed_resultant_nonzero
end
end AspisV8.QuadraticResultantDescent
