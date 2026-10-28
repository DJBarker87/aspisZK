import Op4P_Extract.Funs
import MultiproofConeStrictScan
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op4P_Refinement
attribute [local instance] Classical.propDecidable

/-- Structural identity of the two pure recursive source emissions. This
compares functions, without evaluating any concrete 57,607-byte recurrence. -/
theorem scanner_emission :
    Op4P_Extract.Op4P_reference.parser_reference.scan =
      MultiproofParserRef.parser_reference.scan := by
  delta Op4P_Extract.Op4P_reference.parser_reference.scan
    MultiproofParserRef.parser_reference.scan
    Op4P_Extract.Op4P_reference.parser_reference.opening_rows
    MultiproofParserRef.parser_reference.opening_rows
    Op4P_Extract.Op4P_reference.parser_reference.opening_scan
    MultiproofParserRef.parser_reference.opening_scan
    Op4P_Extract.Op4P_reference.parser_reference.canonical_words
    MultiproofParserRef.parser_reference.canonical_words
    Op4P_Extract.Op4P_reference.reference.check_values
    MultiproofParserRef.reference.check_values
  rfl

/-- Total Result-valued interpretation on the deployed byte length. -/
theorem reference_total (proof : Slice U8) (length : proof.val.length = 57607) :
    Op4P_Extract.Op4P_reference.canonical_scan proof =
      ok (if OraclePortCompactDraft.scan (MultiproofConeCanonical.bytesOf proof.val)
        then .Ok () else .Err .Parse) := by
  rw [Op4P_Extract.Op4P_reference.canonical_scan,scanner_emission,
    MultiproofConeStrictScan.scan_total proof length]
  simp only [bind_tc_ok]
  split <;> simp_all

#print axioms scanner_emission
#print axioms reference_total
end AspisR1.Op4P_Refinement
end
