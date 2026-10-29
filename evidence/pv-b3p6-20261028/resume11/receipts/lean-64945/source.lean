import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/extension_limbs#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_extension_limbs_0 : String := "[\"fn\",\"extension_limbs\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"[\",\"u32\",\";\",\"4\",\"]\",\"{\",\"[\",\"value\",\".\",\"c0\",\".\",\"a\",\".\",\"0\",\",\",\"value\",\".\",\"c0\",\".\",\"b\",\".\",\"0\",\",\",\"value\",\".\",\"c1\",\".\",\"a\",\".\",\"0\",\",\",\"value\",\".\",\"c1\",\".\",\"b\",\".\",\"0\",\"]\",\"}\"]"
def owned_tokens11_poseidon_extension_limbs_0 : String := "[\"fn\",\"extension_limbs\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"[\",\"u32\",\";\",\"4\",\"]\",\"{\",\"[\",\"value\",\".\",\"c0\",\".\",\"a\",\".\",\"0\",\",\",\"value\",\".\",\"c0\",\".\",\"b\",\".\",\"0\",\",\",\"value\",\".\",\"c1\",\".\",\"a\",\".\",\"0\",\",\",\"value\",\".\",\"c1\",\".\",\"b\",\".\",\"0\",\"]\",\"}\"]"
theorem body_identity11_poseidon_extension_limbs_0 : source_tokens11_poseidon_extension_limbs_0 = owned_tokens11_poseidon_extension_limbs_0 :=
  token_identity11 source_tokens11_poseidon_extension_limbs_0
theorem body_interpretation11_poseidon_extension_limbs_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_extension_limbs_0 = interpret owned_tokens11_poseidon_extension_limbs_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_extension_limbs_0
#print axioms body_identity11_poseidon_extension_limbs_0
#print axioms body_interpretation11_poseidon_extension_limbs_0
end PV_B3P_Binding11227
