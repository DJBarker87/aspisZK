import CircleGRSLinearity
import AspisFormal.K1.V7Tag73ExactGRSConversion

/-! The actual selected 1024-dimensional circle-code numerator image is a
linear submodule of QM31[X], not the full degree-at-most-1024 ambient space.
V7's exact degree and injectivity proofs are reused unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedGRSSubmodule
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7Tag73ExactGRSConversion
noncomputable section

theorem numeratorMap_apply {k : Type*} [Field k] (message : Fin 1024 → k) :
    CircleGRSLinearity.numeratorMessage message =
      AspisV5FriCircleEncoderDistance.circleNumerator
        (AspisV5FriInitialCircleEncoderIdentity.initialP0 message)
        (AspisV5FriInitialCircleEncoderIdentity.initialP1 message) := rfl

abbrev K := QM31Exact
abbrev Message := Fin 1024 → K

def encoder : Message →ₗ[K] K[X] := CircleGRSLinearity.numeratorMessage

theorem encoder_eq (message : Message) :
    encoder message = exactCircleGRSPolynomial message := by
  change CircleGRSLinearity.numeratorMessage message = _
  exact (numeratorMap_apply message).trans
    (exactCircleGRSPolynomial_eq_released message).symm

def originalCode : Submodule K K[X] := LinearMap.range encoder

theorem mem_originalCode (p : K[X]) :
    p ∈ originalCode ↔ ∃ message : Message, exactCircleGRSPolynomial message = p := by
  change (∃ message : Message, encoder message = p) ↔ _
  constructor
  · rintro ⟨message, equal⟩
    exact ⟨message, (encoder_eq message).symm.trans equal⟩
  · rintro ⟨message, equal⟩
    exact ⟨message, (encoder_eq message).trans equal⟩

theorem encoder_injective : Function.Injective encoder := by
  intro left right equal
  apply exactCircleGRSPolynomial_injective
  exact (encoder_eq left).symm.trans (equal.trans (encoder_eq right))

theorem member_degree (p : K[X]) (member : p ∈ originalCode) :
    p.natDegree ≤ 1024 := by
  obtain ⟨message, rfl⟩ := (mem_originalCode p).mp member
  exact exactCircleGRSPolynomial_degree_le message

/-- Every submodule-valued coefficient tuple has actual natural-coordinate
messages, unique coordinatewise. This is a mathematical inverse, not an
algorithmic decoder. -/
theorem components_lift {n : Nat} (p : Fin n → K[X])
    (members : ∀ j, p j ∈ originalCode) :
    ∃ messages : Fin n → Message,
      (∀ j, exactCircleGRSPolynomial (messages j) = p j) ∧
      ∀ other : Fin n → Message,
        (∀ j, exactCircleGRSPolynomial (other j) = p j) → other = messages := by
  classical
  have existsMessage : ∀ j, ∃ message : Message,
      exactCircleGRSPolynomial message = p j :=
    fun j => (mem_originalCode (p j)).mp (members j)
  choose messages encoded using existsMessage
  refine ⟨messages, encoded, ?_⟩
  intro other same
  funext j
  exact exactCircleGRSPolynomial_injective ((same j).trans (encoded j).symm)

#print axioms encoder_eq
#print axioms mem_originalCode
#print axioms encoder_injective
#print axioms member_degree
#print axioms components_lift
end
end AspisV8.SelectedGRSSubmodule
