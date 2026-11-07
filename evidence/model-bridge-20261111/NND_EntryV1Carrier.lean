import NND_RegistryV2Carrier
set_option autoImplicit false
namespace NND_Carrier
def entryV1 (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) : RSL.EntryV1 :=
 { status := status x.status,
   statement_version := byte x.statement_version,
   bump := byte x.bump,
   pool := key x.pool,
   verifier_program := key x.verifier_program,
   profile_binding := key x.profile_binding,
   release_binding := key x.release_binding,
   activation_slot := slot x.activation_slot,
   retirement_slot := slot x.retirement_slot,
   policy_binding := key x.policy_binding }
def unentryV1 (x : RSL.EntryV1) : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1 :=
 { status := unstatus x.status,
   statement_version := unbyte x.statement_version,
   bump := unbyte x.bump,
   pool := unkey x.pool,
   verifier_program := unkey x.verifier_program,
   profile_binding := unkey x.profile_binding,
   release_binding := unkey x.release_binding,
   activation_slot := unslot x.activation_slot,
   retirement_slot := unslot x.retirement_slot,
   policy_binding := unkey x.policy_binding }
@[simp] theorem entryV1_back (x : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) : unentryV1 (entryV1 x) = x := by
 cases x
 simp [entryV1,unentryV1]
#print axioms entryV1_back
@[simp] theorem entryV1_forth (x : RSL.EntryV1) : entryV1 (unentryV1 x) = x := by
 cases x
 simp [entryV1,unentryV1]
#print axioms entryV1_forth
end NND_Carrier
