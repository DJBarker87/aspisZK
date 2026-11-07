import NND_RegistryV1Carrier
set_option autoImplicit false
namespace NND_Carrier
def registryV2 (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : RSL.RegistryV2 :=
 { flags := byte x.flags,
   bump := byte x.bump,
   pool := key x.pool,
   authority := key x.authority,
   policy_binding := key x.policy_binding,
   generation := slot x.generation,
   minimum_activation_delay_slots := slot x.minimum_activation_delay_slots,
   registry_program := key x.registry_program,
   loader_program := key x.loader_program,
   programdata_address := key x.programdata_address,
   programdata_bump := byte x.programdata_bump,
   executable_hash := key x.executable_hash }
def unregistryV2 (x : RSL.RegistryV2) : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 :=
 { flags := unbyte x.flags,
   bump := unbyte x.bump,
   pool := unkey x.pool,
   authority := unkey x.authority,
   policy_binding := unkey x.policy_binding,
   generation := unslot x.generation,
   minimum_activation_delay_slots := unslot x.minimum_activation_delay_slots,
   registry_program := unkey x.registry_program,
   loader_program := unkey x.loader_program,
   programdata_address := unkey x.programdata_address,
   programdata_bump := unbyte x.programdata_bump,
   executable_hash := unkey x.executable_hash }
@[simp] theorem registryV2_back (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) : unregistryV2 (registryV2 x) = x := by
 cases x
 simp [registryV2,unregistryV2]
#print axioms registryV2_back
@[simp] theorem registryV2_forth (x : RSL.RegistryV2) : registryV2 (unregistryV2 x) = x := by
 cases x
 simp [registryV2,unregistryV2]
#print axioms registryV2_forth
end NND_Carrier
