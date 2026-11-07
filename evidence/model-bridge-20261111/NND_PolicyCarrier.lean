import NND_PoolIdentityCarrier
set_option autoImplicit false
namespace NND_Carrier
def policy (x : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : RSL.VerifierPolicy :=
 { flags := byte x.flags,
   registry_program := key x.registry_program,
   registry_authority := key x.registry_authority,
   policy_binding := key x.policy_binding }
theorem policy_injective : Function.Injective policy := by
 intro x y h
 cases x
 cases y
 simp only [policy,RSL.VerifierPolicy.mk.injEq,byte_eq_iff,key_eq_iff] at h
 exact AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1.mk.injEq.mpr h
@[simp] theorem policy_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : policy x = policy y ↔ x = y :=
 ⟨fun h => policy_injective h,congrArg policy⟩
#print axioms policy_injective
#print axioms policy_eq_iff
end NND_Carrier
