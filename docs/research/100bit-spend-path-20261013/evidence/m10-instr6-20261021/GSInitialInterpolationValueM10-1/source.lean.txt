import GSProtocolBasisMirrorM10
import GSInterpolationFullWorkM10
import RRConcreteWriterM10
import GSFixedInputDecoderFamily
import SharedFiniteMaterializationM10

/-! Full interpolation and RR traversal, materialized over all 29+5 calls.
The scalar/normalization C and terminal T tariffs remain explicit. Their
implementation adequacy is not inferred just from this value equality. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSInitialInterpolationValueM10
open CompPoly GSFixedInputDecoderFamily
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

attribute [local irreducible] GSProtocolBasisMirrorM10.basis
  GSInterpolationFullWorkM10.eval GSConcreteInterpolation.initial GSConcreteInterpolation.final
  GSConcreteInterpolation.initialState GSConcreteInterpolation.finalState
  RRConcreteWriterM10.recover RRTraversalWriterM10.budget

def stateTariff (M : Nat) : Nat := 100*(M+114)^2

def initialInterpolation (points : Array (K × K)) : Option (CBivariate K) × Nat :=
  GSInterpolationFullWorkM10.eval 114689
    (GSProtocolBasisMirrorM10.basis 1024 114689 112) points

theorem initialInterpolation_value (points : Array (K × K)) :
    (initialInterpolation points).1 = GSConcreteInterpolation.initial points := by
  unfold initialInterpolation GSConcreteInterpolation.initial
  rw [GSProtocolBasisMirrorM10.value]
  exact GSInterpolationFullWorkM10.value 114689 _ _ GSConcreteInterpolation.initialParams rfl

#check @initialInterpolation_value

#print axioms initialInterpolation_value
end AspisR1.GSInitialInterpolationValueM10
end
