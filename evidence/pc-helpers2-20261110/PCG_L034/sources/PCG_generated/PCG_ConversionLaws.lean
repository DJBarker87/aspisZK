import PCG_ConversionRef.Funs
import PCG_ErrorLaws
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_ConversionLaws
/-- Every DepositInstructionFormatErrorV1 arm is represented by the native
constructor harness. The output is the full typed enum, with no ABI quotient. -/
theorem row_287 (e : PCG_ConversionRef.DepositInstructionFormatErrorV1) :
 PCG_ConversionRef.reference287 e = ok .InvalidDeposit := rfl

/-- The reference retains the full26-variant ProgramError carrier, including
BorshIoError(String); this conversion returns its exact InvalidInstructionData arm. -/
theorem row_288 (e : PCG_ConversionRef.PoolInstructionFormatErrorV1) :
 PCG_ConversionRef.reference288 e = ok .InvalidInstructionData := rfl
#print axioms row_287
#print axioms row_288
end PCG_ConversionLaws
