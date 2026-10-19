import GSInterpolationBackendWitness
import GSRawStateConstructorContractV1

set_option autoImplicit false
namespace AspisR1.GSConcreteInterpolation
open CompPoly CompPoly.GuruswamiSudan
open AspisR1.RRConcreteState AspisR1.GSRawStateCoefficientBridge

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def initialParams : GSInterpParams := ⟨1025, 3, 114689⟩
def finalParams : GSInterpParams := ⟨256, 3, 28673⟩

def initial (points : Array (K × K)) : Option (CBivariate K) :=
  denseInterpolateWithBasisAndKernel (denseLinearKernelContext K)
    (AspisWide.GSInterpolationRowBasis.basis 1024 114689 112) points initialParams

def final (points : Array (K × K)) : Option (CBivariate K) :=
  denseInterpolateWithBasisAndKernel (denseLinearKernelContext K)
    (AspisWide.GSInterpolationRowBasis.basis 255 28673 112) points finalParams

theorem initial_exists (points : Array (K × K)) (hs : points.size = 1048576) :
    ∃ Q, initial points = some Q ∧ ValidInterpolationWitness points initialParams Q :=
  AspisWide.GSInterpolationBackendWitness.initial_dense_witness points hs

theorem final_exists (points : Array (K × K)) (hs : points.size = 262144) :
    ∃ Q, final points = some Q ∧ ValidInterpolationWitness points finalParams Q :=
  AspisWide.GSInterpolationBackendWitness.final_dense_witness points hs

theorem initial_spec (points : Array (K × K)) (hs : points.size = 1048576)
    (Q : CBivariate K) (hrun : initial points = some Q) :
    ValidInterpolationWitness points initialParams Q := by
  obtain ⟨R, hR, hw⟩ := initial_exists points hs
  have he : Q = R := Option.some.inj (hrun.symm.trans hR)
  subst R
  exact hw

theorem final_spec (points : Array (K × K)) (hs : points.size = 262144)
    (Q : CBivariate K) (hrun : final points = some Q) :
    ValidInterpolationWitness points finalParams Q := by
  obtain ⟨R, hR, hw⟩ := final_exists points hs
  have he : Q = R := Option.some.inj (hrun.symm.trans hR)
  subst R
  exact hw

def initialState (Q : CBivariate K) : RawState K := gsState Q 114689 112
def finalState (Q : CBivariate K) : RawState K := gsState Q 28673 112

/-- Every actual successful backend result supplies all raw recovery premises.
No external nonzeroness or coefficient/canonicality hypothesis is introduced. -/
theorem initial_state_contract (points : Array (K × K))
    (hs : points.size = 1048576) (Q : CBivariate K) (hrun : initial points = some Q) :
    model (initialState Q) = CBivariate.toPoly Q ∧
    (∀ i ≤ (initialState Q).maxX,
      (RRVectorRowPolynomialBridge.inputPolynomial (initialState Q).rows i).natDegree ≤ 112) ∧
    model (initialState Q) ≠ 0 := by
  have hw := initial_spec points hs Q hrun
  have hd := hw.2.1
  change Q.natWeightedDegree 1 1024 ≤ 114689 at hd
  have hc := gsState_contract Q 114689 112 1024 hd (by norm_num)
  dsimp only [initialState, gsState]
  dsimp only [gsState] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2 hw.1⟩

theorem final_state_contract (points : Array (K × K))
    (hs : points.size = 262144) (Q : CBivariate K) (hrun : final points = some Q) :
    model (finalState Q) = CBivariate.toPoly Q ∧
    (∀ i ≤ (finalState Q).maxX,
      (RRVectorRowPolynomialBridge.inputPolynomial (finalState Q).rows i).natDegree ≤ 112) ∧
    model (finalState Q) ≠ 0 := by
  have hw := final_spec points hs Q hrun
  have hd := hw.2.1
  change Q.natWeightedDegree 1 255 ≤ 28673 at hd
  have hc := gsState_contract Q 28673 112 255 hd (by norm_num)
  dsimp only [finalState, gsState]
  dsimp only [gsState] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2 hw.1⟩

#print axioms initial
#print axioms final
#print axioms initial_exists
#print axioms final_exists
#print axioms initial_state_contract
#print axioms final_state_contract
end AspisR1.GSConcreteInterpolation
