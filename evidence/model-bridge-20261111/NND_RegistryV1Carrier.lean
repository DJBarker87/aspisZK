import NND_StatusCarrier
set_option autoImplicit false
namespace NND_Carrier
def registryV1 (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : RSL.RegistryV1 :=
 { flags := byte x.flags,
   bump := byte x.bump,
   pool := key x.pool,
   authority := key x.authority,
   policy_binding := key x.policy_binding,
   generation := slot x.generation,
   minimum_activation_delay_slots := slot x.minimum_activation_delay_slots }
def unregistryV1 (x : RSL.RegistryV1) : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1 :=
 { flags := unbyte x.flags,
   bump := unbyte x.bump,
   pool := unkey x.pool,
   authority := unkey x.authority,
   policy_binding := unkey x.policy_binding,
   generation := unslot x.generation,
   minimum_activation_delay_slots := unslot x.minimum_activation_delay_slots }
@[simp] theorem registryV1_back (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) : unregistryV1 (registryV1 x) = x := by
 cases x
 simp [registryV1,unregistryV1]
#print axioms registryV1_back
@[simp] theorem registryV1_forth (x : RSL.RegistryV1) : registryV1 (unregistryV1 x) = x := by
 cases x
 simp [registryV1,unregistryV1]
#print axioms registryV1_forth
end NND_Carrier
