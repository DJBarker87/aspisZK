import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/lift_m31#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_lift_m31_0 : String := "[\"fn\",\"lift_m31\",\"(\",\"value\",\":\",\"M31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"QM31\",\":\",\":\",\"from_cm31\",\"(\",\"CM31\",\":\",\":\",\"from_m31\",\"(\",\"value\",\")\",\")\",\"}\"]"
def owned_tokens11_terminal_lift_m31_0 : String := "[\"fn\",\"lift_m31\",\"(\",\"value\",\":\",\"M31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"QM31\",\":\",\":\",\"from_cm31\",\"(\",\"CM31\",\":\",\":\",\"from_m31\",\"(\",\"value\",\")\",\")\",\"}\"]"
theorem body_identity11_terminal_lift_m31_0 : source_tokens11_terminal_lift_m31_0 = owned_tokens11_terminal_lift_m31_0 :=
  token_identity11 source_tokens11_terminal_lift_m31_0
theorem body_interpretation11_terminal_lift_m31_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_lift_m31_0 = interpret owned_tokens11_terminal_lift_m31_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_lift_m31_0
#print axioms body_identity11_terminal_lift_m31_0
#print axioms body_interpretation11_terminal_lift_m31_0
end PV_B3P_Binding11227
