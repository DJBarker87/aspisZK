import LPl_Check
import LPl_EcheckResult
import LPl_ValidateResult
import LPn_ExpandTrace
namespace KSD_LeafSelection
abbrev check_values := compact.check_values
abbrev echeck := verifier.echeck
abbrev validate_record_fields := r1_wire.validate_record_fields
abbrev expand_values := compact.expand_values
#print axioms LPl.Check.native_result
#print axioms LPl.Echeck.native_result
#print axioms LPl.Validate.native_result
end KSD_LeafSelection
