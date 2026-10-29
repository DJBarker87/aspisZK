import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/extension_from_raw_limbs#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_extension_from_raw_limbs_0 : String := "[\"fn\",\"extension_from_raw_limbs\",\"(\",\"limbs\",\":\",\"[\",\"u64\",\";\",\"4\",\"]\",\")\",\"-\",\">\",\"QM31\",\"{\",\"QM31\",\"{\",\"c0\",\":\",\"CM31\",\":\",\":\",\"new\",\"(\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"0\",\"]\",\")\",\",\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"1\",\"]\",\")\",\")\",\",\",\"c1\",\":\",\"CM31\",\":\",\":\",\"new\",\"(\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"2\",\"]\",\")\",\",\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"3\",\"]\",\")\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_poseidon_extension_from_raw_limbs_0 : String := "[\"fn\",\"extension_from_raw_limbs\",\"(\",\"limbs\",\":\",\"[\",\"u64\",\";\",\"4\",\"]\",\")\",\"-\",\">\",\"QM31\",\"{\",\"QM31\",\"{\",\"c0\",\":\",\"CM31\",\":\",\":\",\"new\",\"(\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"0\",\"]\",\")\",\",\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"1\",\"]\",\")\",\")\",\",\",\"c1\",\":\",\"CM31\",\":\",\":\",\"new\",\"(\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"2\",\"]\",\")\",\",\",\"M31\",\":\",\":\",\"reduce_u62\",\"(\",\"limbs\",\"[\",\"3\",\"]\",\")\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_poseidon_extension_from_raw_limbs_0 : source_tokens11_poseidon_extension_from_raw_limbs_0 = owned_tokens11_poseidon_extension_from_raw_limbs_0 :=
  token_identity11 source_tokens11_poseidon_extension_from_raw_limbs_0
theorem body_interpretation11_poseidon_extension_from_raw_limbs_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_extension_from_raw_limbs_0 = interpret owned_tokens11_poseidon_extension_from_raw_limbs_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_extension_from_raw_limbs_0
#print axioms body_identity11_poseidon_extension_from_raw_limbs_0
#print axioms body_interpretation11_poseidon_extension_from_raw_limbs_0
end PV_B3P_Binding11227
