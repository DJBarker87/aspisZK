import NND_EntryV1Carrier
set_option autoImplicit false
namespace NND_Carrier
def entryV2 (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) : RSL.EntryV2 :=
 { status := status x.status,
   statement_version := byte x.statement_version,
   bump := byte x.bump,
   pool := key x.pool,
   verifier_program := key x.verifier_program,
   profile_binding := key x.profile_binding,
   release_binding := key x.release_binding,
   loader_program := key x.loader_program,
   programdata_address := key x.programdata_address,
   programdata_bump := byte x.programdata_bump,
   executable_hash := key x.executable_hash,
   expected_upgrade_authority := key x.expected_upgrade_authority,
   activation_slot := slot x.activation_slot,
   retirement_slot := slot x.retirement_slot,
   policy_binding := key x.policy_binding }
def unentryV2 (x : RSL.EntryV2) : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2 :=
 { status := unstatus x.status,
   statement_version := unbyte x.statement_version,
   bump := unbyte x.bump,
   pool := unkey x.pool,
   verifier_program := unkey x.verifier_program,
   profile_binding := unkey x.profile_binding,
   release_binding := unkey x.release_binding,
   loader_program := unkey x.loader_program,
   programdata_address := unkey x.programdata_address,
   programdata_bump := unbyte x.programdata_bump,
   executable_hash := unkey x.executable_hash,
   expected_upgrade_authority := unkey x.expected_upgrade_authority,
   activation_slot := unslot x.activation_slot,
   retirement_slot := unslot x.retirement_slot,
   policy_binding := unkey x.policy_binding }
@[simp] theorem entryV2_back (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) : unentryV2 (entryV2 x) = x := by
 cases x
 simp [entryV2,unentryV2]
#print axioms entryV2_back
@[simp] theorem entryV2_forth (x : RSL.EntryV2) : entryV2 (unentryV2 x) = x := by
 cases x
 simp [entryV2,unentryV2]
#print axioms entryV2_forth
end NND_Carrier
