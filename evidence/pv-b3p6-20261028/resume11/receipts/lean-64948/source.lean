import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/interpolate_three_constant_limb#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_interpolate_three_constant_limb_0 : String := "[\"fn\",\"interpolate_three_constant_limb\",\"(\",\"weight0\",\":\",\"u32\",\",\",\"weight1\",\":\",\"u32\",\",\",\"weight2\",\":\",\"u32\",\",\",\"constant0\",\":\",\"u32\",\",\",\"constant1\",\":\",\"u32\",\",\",\"constant2\",\":\",\"u32\",\",\",\")\",\"-\",\">\",\"M31\",\"{\",\"M31\",\":\",\":\",\"reduce_u64\",\"(\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight0\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant0\",\")\",\"+\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight1\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant1\",\")\",\"+\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight2\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant2\",\")\",\",\",\")\",\"}\"]"
def owned_tokens11_poseidon_interpolate_three_constant_limb_0 : String := "[\"fn\",\"interpolate_three_constant_limb\",\"(\",\"weight0\",\":\",\"u32\",\",\",\"weight1\",\":\",\"u32\",\",\",\"weight2\",\":\",\"u32\",\",\",\"constant0\",\":\",\"u32\",\",\",\"constant1\",\":\",\"u32\",\",\",\"constant2\",\":\",\"u32\",\",\",\")\",\"-\",\">\",\"M31\",\"{\",\"M31\",\":\",\":\",\"reduce_u64\",\"(\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight0\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant0\",\")\",\"+\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight1\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant1\",\")\",\"+\",\"u64\",\":\",\":\",\"from\",\"(\",\"weight2\",\")\",\"*\",\"u64\",\":\",\":\",\"from\",\"(\",\"constant2\",\")\",\",\",\")\",\"}\"]"
theorem body_identity11_poseidon_interpolate_three_constant_limb_0 : source_tokens11_poseidon_interpolate_three_constant_limb_0 = owned_tokens11_poseidon_interpolate_three_constant_limb_0 :=
  token_identity11 source_tokens11_poseidon_interpolate_three_constant_limb_0
theorem body_interpretation11_poseidon_interpolate_three_constant_limb_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_interpolate_three_constant_limb_0 = interpret owned_tokens11_poseidon_interpolate_three_constant_limb_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_interpolate_three_constant_limb_0
#print axioms body_identity11_poseidon_interpolate_three_constant_limb_0
#print axioms body_interpretation11_poseidon_interpolate_three_constant_limb_0
end PV_B3P_Binding11227
