import R1Z.PV_RDCD5_ParserTransport
import R1Z.PV_RDCD5_V197
set_option autoImplicit false
namespace R1Z.PV_RDCD5_ParserErrors
open Aeneas Aeneas.Std Result
/-- Original source still panics on the empty slice. -/
theorem existing_empty :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) = fail .panic := by rfl
/-- Corrected owned model now has exactly the source's constructor. -/
theorem owned_empty : PV_RDCD4_BytesSource.qm [] = fail .panic := by
  exact PV_RDCD5_V197.short_failure [] (by simp)
/-- Supersedes the old mismatch: complete Result equality on every input. -/
theorem carrier_agreement (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes =
      PV_RDCD4_BytesSource.qm bytes.val := PV_RDCD5_ParserTransport.quartic bytes
#print axioms existing_empty
#print axioms owned_empty
#print axioms carrier_agreement
end R1Z.PV_RDCD5_ParserErrors
