import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- copy/boxed_at_point#0; complete source and owned lexical token sequences. -/
def source_tokens11_copy_boxed_at_point_0 : String := "[\"fn\",\"boxed_at_point\",\"(\",\"point\",\":\",\"&\",\"[\",\"QM31\",\";\",\"10\",\"]\",\")\",\"-\",\">\",\"Self\",\"{\",\"Self\",\":\",\":\",\"at_point\",\"(\",\"point\",\")\",\"}\"]"
def owned_tokens11_copy_boxed_at_point_0 : String := "[\"fn\",\"boxed_at_point\",\"(\",\"point\",\":\",\"&\",\"[\",\"QM31\",\";\",\"10\",\"]\",\")\",\"-\",\">\",\"Self\",\"{\",\"Self\",\":\",\":\",\"at_point\",\"(\",\"point\",\")\",\"}\"]"
theorem body_identity11_copy_boxed_at_point_0 : source_tokens11_copy_boxed_at_point_0 = owned_tokens11_copy_boxed_at_point_0 :=
  token_identity11 source_tokens11_copy_boxed_at_point_0
theorem body_interpretation11_copy_boxed_at_point_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_copy_boxed_at_point_0 = interpret owned_tokens11_copy_boxed_at_point_0 :=
  interpret_identity11 interpret _ _ body_identity11_copy_boxed_at_point_0
#print axioms body_identity11_copy_boxed_at_point_0
#print axioms body_interpretation11_copy_boxed_at_point_0
end PV_B3P_Binding11227
