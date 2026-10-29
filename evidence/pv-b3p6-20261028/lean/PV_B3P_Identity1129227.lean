import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/cm31_mul_r#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_cm31_mul_r_0 : String := "[\"fn\",\"cm31_mul_r\",\"(\",\"value\",\":\",\"CM31\",\")\",\"-\",\">\",\"CM31\",\"{\",\"CM31\",\":\",\":\",\"new\",\"(\",\"value\",\".\",\"a\",\".\",\"double\",\"(\",\")\",\".\",\"sub\",\"(\",\"value\",\".\",\"b\",\")\",\",\",\"value\",\".\",\"a\",\".\",\"add\",\"(\",\"value\",\".\",\"b\",\".\",\"double\",\"(\",\")\",\")\",\")\",\"}\"]"
def owned_tokens11_field_cm31_mul_r_0 : String := "[\"fn\",\"cm31_mul_r\",\"(\",\"value\",\":\",\"CM31\",\")\",\"-\",\">\",\"CM31\",\"{\",\"CM31\",\":\",\":\",\"new\",\"(\",\"value\",\".\",\"a\",\".\",\"double\",\"(\",\")\",\".\",\"sub\",\"(\",\"value\",\".\",\"b\",\")\",\",\",\"value\",\".\",\"a\",\".\",\"add\",\"(\",\"value\",\".\",\"b\",\".\",\"double\",\"(\",\")\",\")\",\")\",\"}\"]"
theorem body_identity11_field_cm31_mul_r_0 : source_tokens11_field_cm31_mul_r_0 = owned_tokens11_field_cm31_mul_r_0 :=
  token_identity11 source_tokens11_field_cm31_mul_r_0
theorem body_interpretation11_field_cm31_mul_r_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_cm31_mul_r_0 = interpret owned_tokens11_field_cm31_mul_r_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_cm31_mul_r_0
#print axioms body_identity11_field_cm31_mul_r_0
#print axioms body_interpretation11_field_cm31_mul_r_0
end PV_B3P_Binding11227
