import NHT_COMBINED_IMPORT
import NHV_NEO_QuadraticTotal
import S8OwnedP6QMParserTransport

set_option autoImplicit false
namespace NEO_QModelBinding
open Aeneas Aeneas.Std Result AspisR1
open S8OwnedP6FieldParserTransport

theorem complex (bytes : Slice U8) (bound : 8≤bytes.val.length) :
 NEO_WindowV2.complex bytes =
 mapResult (Option.map (fun x => NEO_ComplexReference.observe (cToCandidate x)))
  (S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes) := by
 rw [NEO_ComplexTotal.result bytes bound]
 unfold NEO_ComplexReference.cohort
 rw [← cm_parser_eq bytes]
 cases h : S8OwnedP6.aspis_core.field.CM31.from_le_bytes bytes <;> try rfl
 rename_i o
 cases o <;> rfl

theorem quadratic (bytes : Slice U8) (bound : 16≤bytes.val.length) :
 NEO_WindowV2.quadratic bytes =
 mapResult (Option.map (fun x => NEO_QuadraticCuts.observe (qToCandidate x)))
  (S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes) := by
 rw [NEO_QuadraticTotal.result bytes bound]
 unfold NEO_QuadraticCuts.cohort
 rw [← S8OwnedP6QMParserTransport.qm_parser_eq bytes]
 cases h : S8OwnedP6.aspis_core.field.QM31.from_le_bytes bytes <;> try rfl
 rename_i o
 cases o <;> rfl

#print axioms complex
#print axioms quadratic
end NEO_QModelBinding
