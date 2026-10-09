import SameBodySequentialCodec
import SelectedWireBytes

/-!
# One-body semantic fixed fields and roots

The selected semantic transcript consumes both the 697 canonical fixed fields
and the two 26-byte commitment roots.  This adapter obtains all three from one
successful parse of the submitted body.  It prevents a semantic execution from
being paired with independently supplied roots while leaving the later proof
that those body roots equal the chronological commitment-cut roots to the
authentication layer.

This is a functional byte-model constructor, not a Rust/Aeneas refinement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SameBodySemanticWire

open AspisV5ComponentCQM31TowerExact
open AspisV8.SameBodySequentialCodec

abbrev Bytes := List UInt8
abbrev K := QM31Exact
abbrev Root := Fin 26 → UInt8

noncomputable section

structure Wire where
  values : List K
  roots : Fin 2 → Root

def ofSelected (wire : AspisV8.SelectedWireBytes.Wire) : Wire where
  values := wire.values
  roots := fun phase byte => UInt8.ofFin (wire.roots phase byte)

/-- Parse once: fixed fields and roots cannot come from different bodies. -/
def parse (body : Bytes) : Option Wire :=
  (AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin)).map ofSelected

theorem parse_success (body : Bytes) (wire : Wire)
    (success : parse body = some wire) :
    ∃ selected : AspisV8.SelectedWireBytes.Wire,
      AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin) = some selected ∧
      wire = ofSelected selected := by
  unfold parse at success
  cases parsed : AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin) with
  | none => simp [parsed] at success
  | some selected =>
      simp only [parsed, Option.map_some, Option.some.injEq] at success
      exact ⟨selected, rfl, success.symm⟩

/-- The value list is the literal sequential canonical parser's result for
the same body; there is no second fixed-field input. -/
theorem fields_exact (body : Bytes) (wire : Wire)
    (success : parse body = some wire) :
    fields (body.map UInt8.toFin) = some wire.values := by
  obtain ⟨selected, selectedParse, rfl⟩ := parse_success body wire success
  rw [fields_eq_parseFixed]
  exact (AspisV8.SelectedWireBytes.parse_success
    (body.map UInt8.toFin) selected selectedParse).1

/-- Both semantic roots are projections of the selected parser result from
the same body.  Authentication later proves equality to the actual root cuts. -/
theorem roots_exact (body : Bytes) (wire : Wire)
    (success : parse body = some wire) :
    ∃ selected : AspisV8.SelectedWireBytes.Wire,
      AspisV8.SelectedWireBytes.parse (body.map UInt8.toFin) = some selected ∧
      ∀ phase byte,
        wire.roots phase byte = UInt8.ofFin (selected.roots phase byte) := by
  obtain ⟨selected, selectedParse, rfl⟩ := parse_success body wire success
  exact ⟨selected, selectedParse, fun _ _ => rfl⟩

#print axioms parse_success
#print axioms fields_exact
#print axioms roots_exact

end
end AspisV8Completion.SameBodySemanticWire
