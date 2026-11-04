import R0Z.HonestView

/-! R0's batched opening block as an instance of `HonestView.BatchedLayer`
(job R1-0, DESIGN-R1-PRIVACY-MODEL §2.2). The seven opening-relation
coefficients and the 256 folded coefficients are read from the chord-quotient
batch exactly as the pre-refactor `linearPayload` did (HonestView, R0 cells
`.openingCoeff` and `.finalCoeff`). No proof here evaluates a concrete index set. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.R0Batched
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisWide.InitialEncoder
open AspisWide.Agreement AspisR0.Opening AspisR0.Chord AspisR0.ChordGeometry
open AspisV5ComponentCConcreteFoldLinearity
open AspisR0.PolynomialPair AspisR0.RoundNormalization AspisR0.Fold
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- R0's batched cells: opening-relation and final-fold coefficients. -/
inductive R0Bat
  | openingCoeff (coefficient : Fin 7)
  | finalCoeff (coefficient : Fin 256)
  deriving DecidableEq

/-- The pre-refactor R0 read of the batched block (HonestView, former
`linearPayload` branches `.openingCoeff`/`.finalCoeff`). -/
def r0Read (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) : Trace K →ₗ[K] (R0Bat → K) :=
  LinearMap.pi fun b => match b with
  | .openingCoeff i => (Polynomial.lcoeff K i.val).comp
      ((relationLinear (openingWeights π ch)).comp (batchLinear π ch))
  | .finalCoeff i => (LinearMap.proj i).comp ((foldLinear (ch.opening 3)).comp (batchLinear π ch))

instance instBatchedLayer : BatchedLayer K R0Bat where
  read := r0Read

/-- R0 payload cells, as before the refactor. -/
abbrev R0Payload (K : Type) := Payload K R0Bat

attribute [local irreducible] batchLinear openingWeights relationLinear

/-- The former `run` branch `.openingCoeff i`. -/
theorem read_openingCoeff (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (i : Fin 7) :
    BatchedLayer.read π ch t (R0Bat.openingCoeff i) =
      (roundPolynomial (batchLinear π ch t) (openingWeights π ch)).coeff i.val := by
  change (Polynomial.lcoeff K i.val) (relationLinear (openingWeights π ch) (batchLinear π ch t)) = _
  rw [Polynomial.lcoeff_apply, relationLinear_apply]

/-- The former `run` branch `.finalCoeff i`. -/
theorem read_finalCoeff (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (i : Fin 256) :
    BatchedLayer.read π ch t (R0Bat.finalCoeff i) =
      foldMessage (ch.opening 3) (batchLinear π ch t) i := by
  change foldLinear (ch.opening 3) (batchLinear π ch t) i = _
  rw [foldLinear_apply]

#print axioms r0Read
#print axioms read_openingCoeff
#print axioms read_finalCoeff
end R0Z.R0Batched
