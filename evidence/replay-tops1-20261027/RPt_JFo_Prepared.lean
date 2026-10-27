import RPt_JFq_State
import RPt_JFq_Root0
import RPt_JFq_Root1
import RPt_JFq_Gamma
import RPt_JFq_Kappa
import RPt_JFq_Alpha0
import RPt_JFq_Alpha1
import RPt_JFq_Rho
import RPt_JFq_Queries
import RPt_JFq_Semantic
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
import RPt_JFq_Claim
import RPt_JFq_Rhs
import RPt_JFq_Power
import RPt_JFo_Weights
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Prepared
open Aeneas Aeneas.Std Result AspisR1Stage2

def value : verifier.Prepared where
  variant := .S2
  roots := Array.make 2#usize [JFq_Root0.value,JFq_Root1.value]
  gamma := JFq_Gamma.scalar
  kappa := JFq_Kappa.scalar
  alpha := Array.make 2#usize [JFq_Alpha0.scalar,JFq_Alpha1.scalar]
  rho := JFq_Rho.scalar
  queries := JFq_Queries.value
  semantic_alpha := JFq_Semantic.value
  z := Array.make 2#usize [⟨JFq_Z0.scalar,JFq_Z1.scalar⟩,⟨JFq_Z2.scalar,JFq_Z3.scalar⟩]
  claim := JFq_Claim.scalar
  state := JFq_State.value

def accumulator : verifier.Accumulator where
  weights := JFo_Weights.value
  rhs := JFq_Rhs.scalar
  power := JFq_Power.scalar
  next := 10#usize

theorem next : accumulator.next=10#usize := rfl
theorem weights_length : accumulator.weights.val.length=64 := JFo_Weights.length

#print axioms next
#print axioms weights_length
end AspisR1.JFo_Prepared
end
