import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Fin
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false
namespace AspisR0.RoundNormalization
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def dot {n : Nat} (q w : Fin n → K) : K := ∑ i, q i * w i

end
end AspisR0.RoundNormalization
