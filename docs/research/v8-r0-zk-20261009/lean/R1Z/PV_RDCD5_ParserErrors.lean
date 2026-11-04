import R1Z.PV_RDCD5_V197
import R1Z.ProverRwSuccessParserSource
set_option autoImplicit false
namespace R1Z.PV_RDCD5_ParserErrors
open Aeneas Aeneas.Std Result
/-- Existing callback parser uses panic for an invalid range. -/
theorem existing_empty :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) = fail .panic := by rfl
/-- The inherited owned model uses a different error constructor. -/
theorem owned_empty : PV_RDCD4_BytesSource.qm [] = fail .arrayOutOfBounds := by
  exact PV_RDCD5_V197.short_failure [] (by simp)
/-- A literal whole-Result identification would therefore be false. -/
theorem carrier_mismatch :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) ≠ PV_RDCD4_BytesSource.qm [] := by
  rw [existing_empty,owned_empty]
  intro h
  cases h
#print axioms existing_empty
#print axioms owned_empty
#print axioms carrier_mismatch
end R1Z.PV_RDCD5_ParserErrors
