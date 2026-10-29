import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/new#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_new_0 : String := "[\"fn\",\"new\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"Self\",\"{\",\"Self\",\"{\",\"components\",\":\",\"[\",\"prepare_component\",\"(\",\"value\",\".\",\"c0\",\")\",\",\",\"prepare_component\",\"(\",\"value\",\".\",\"c1\",\")\",\",\",\"prepare_component\",\"(\",\"value\",\".\",\"c0\",\".\",\"add\",\"(\",\"value\",\".\",\"c1\",\")\",\")\",\",\",\"]\",\",\",\"}\",\"}\"]"
def owned_tokens11_field_new_0 : String := "[\"fn\",\"new\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"Self\",\"{\",\"Self\",\"{\",\"components\",\":\",\"[\",\"prepare_component\",\"(\",\"value\",\".\",\"c0\",\")\",\",\",\"prepare_component\",\"(\",\"value\",\".\",\"c1\",\")\",\",\",\"prepare_component\",\"(\",\"value\",\".\",\"c0\",\".\",\"add\",\"(\",\"value\",\".\",\"c1\",\")\",\")\",\",\",\"]\",\",\",\"}\",\"}\"]"
theorem body_identity11_field_new_0 : source_tokens11_field_new_0 = owned_tokens11_field_new_0 :=
  token_identity11 source_tokens11_field_new_0
theorem body_interpretation11_field_new_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_new_0 = interpret owned_tokens11_field_new_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_new_0
#print axioms body_identity11_field_new_0
#print axioms body_interpretation11_field_new_0
end PV_B3P_Binding11227
