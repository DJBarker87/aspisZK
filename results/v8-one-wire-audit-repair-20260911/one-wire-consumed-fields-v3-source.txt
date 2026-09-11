import SelectedWireBytes

/-!
The same-body fixed-field leaf for the V8 audit repair.

Unlike `SuccessfulCompleteSelectedWire`, this module has no independently
supplied `Program`: every relation field below is projected from one successful
`SelectedWireBytes.parse body`.  It is deliberately only a byte-to-relation
field construction.  The outer semantic functional/claim, public context,
full C1/C2 prefixes, causal strategy and Rust refinement are not represented
as premises disguised as coherence.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000

namespace AspisV8.OneWireConsumedFields
open AspisV8.SelectedWireBytes AspisV8.CanonicalRelationInput
open AspisPool.V7MerkleQueryGrammar
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte

/-- Canonical fixed value at one literal selected-body field index. -/
def fixedAt (wire : Wire) (field : Fin 697) : K :=
  wire.values.getD field.val 0

def semanticField (wire : Wire) (field : Fin 271) : K :=
  fixedAt wire ⟨field.val, by omega⟩

def ordinaryClaim (wire : Wire) (row : Fin 3) (lane : Fin 29) : K :=
  fixedAt wire ⟨271 + 29 * row.val + lane.val, by omega⟩

def inactiveClaim (wire : Wire) : K := fixedAt wire 358

def componentOOD (wire : Wire) (phase : Fin 2) (lane : Fin 29) : K :=
  fixedAt wire ⟨359 + 29 * phase.val + lane.val, by omega⟩

def compactResponse (wire : Wire) (round : Fin 4) (sent : Fin 6) : K :=
  fixedAt wire (relationIndex round sent)

def finalCoefficient (wire : Wire) (coefficient : Fin 256) : K :=
  fixedAt wire (finalIndex coefficient)

/-- All fixed-section values consumed by the isolated selected relation
callback.  This structure has no `Program`, acceptance or ideal-execution
field: it is a transparent bundle of projections from one `Wire`. -/
structure RelationFields where
  semantic : Fin 271 -> K
  claims : Fin 3 -> Fin 29 -> K
  inactive : K
  ood : Fin 2 -> Fin 29 -> K
  responses : Fin 4 -> Fin 6 -> K
  final256 : Fin 256 -> K

def relationFields (wire : Wire) : RelationFields where
  semantic := semanticField wire
  claims := ordinaryClaim wire
  inactive := inactiveClaim wire
  ood := componentOOD wire
  responses := compactResponse wire
  final256 := finalCoefficient wire

/-- Canonical parser success identifies every projected field with its
literal 16-byte decoded value. -/
theorem fixedAt_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire) (field : Fin 697) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body field) = some (fixedAt wire field) :=
  (SelectedWireBytes.fixed_fields body wire parsed).2 field

theorem semanticField_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire) (field : Fin 271) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body ⟨field.val, by omega⟩) =
        some (semanticField wire field) :=
  fixedAt_decoded body wire parsed _

theorem ordinaryClaim_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire)
    (row : Fin 3) (lane : Fin 29) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body
        ⟨271 + 29 * row.val + lane.val, by omega⟩) =
        some (ordinaryClaim wire row lane) :=
  fixedAt_decoded body wire parsed _

theorem inactiveClaim_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body 358) = some (inactiveClaim wire) :=
  fixedAt_decoded body wire parsed _

theorem componentOOD_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire)
    (phase : Fin 2) (lane : Fin 29) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body
        ⟨359 + 29 * phase.val + lane.val, by omega⟩) =
        some (componentOOD wire phase lane) :=
  fixedAt_decoded body wire parsed _

theorem compactResponse_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire)
    (round : Fin 4) (sent : Fin 6) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body (relationIndex round sent)) =
        some (compactResponse wire round sent) :=
  fixedAt_decoded body wire parsed _

theorem finalCoefficient_decoded (body : List Byte) (wire : Wire)
    (parsed : SelectedWireBytes.parse body = some wire)
    (coefficient : Fin 256) :
    AspisV5ComponentCQM31TowerExact.decodeQM31ExactLE
      (CanonicalRelationInput.fieldBytes body (finalIndex coefficient)) =
        some (finalCoefficient wire coefficient) :=
  fixedAt_decoded body wire parsed _

theorem relationFields_transparent (wire : Wire) :
    (relationFields wire).responses = compactResponse wire ∧
    (relationFields wire).final256 = finalCoefficient wire ∧
    (relationFields wire).claims = ordinaryClaim wire ∧
    (relationFields wire).ood = componentOOD wire ∧
    (relationFields wire).inactive = inactiveClaim wire := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms fixedAt_decoded
#print axioms ordinaryClaim_decoded
#print axioms componentOOD_decoded
#print axioms compactResponse_decoded
#print axioms finalCoefficient_decoded
end
end AspisV8.OneWireConsumedFields
