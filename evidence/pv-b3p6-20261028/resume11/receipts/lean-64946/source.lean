import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/external_local_packed#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_external_local_packed_0 : String := "[\"fn\",\"external_local_packed\",\"(\",\"input\",\":\",\"[\",\"QM31\",\";\",\"4\",\"]\",\")\",\"-\",\">\",\"QM31\",\"{\",\"extension_from_raw_limbs\",\"(\",\"external_local_packed_raw\",\"(\",\"input\",\")\",\")\",\"}\"]"
def owned_tokens11_poseidon_external_local_packed_0 : String := "[\"fn\",\"external_local_packed\",\"(\",\"input\",\":\",\"[\",\"QM31\",\";\",\"4\",\"]\",\")\",\"-\",\">\",\"QM31\",\"{\",\"extension_from_raw_limbs\",\"(\",\"external_local_packed_raw\",\"(\",\"input\",\")\",\")\",\"}\"]"
theorem body_identity11_poseidon_external_local_packed_0 : source_tokens11_poseidon_external_local_packed_0 = owned_tokens11_poseidon_external_local_packed_0 :=
  token_identity11 source_tokens11_poseidon_external_local_packed_0
theorem body_interpretation11_poseidon_external_local_packed_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_external_local_packed_0 = interpret owned_tokens11_poseidon_external_local_packed_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_external_local_packed_0
#print axioms body_identity11_poseidon_external_local_packed_0
#print axioms body_interpretation11_poseidon_external_local_packed_0
end PV_B3P_Binding11227
