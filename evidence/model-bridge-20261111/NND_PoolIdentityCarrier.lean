import NND_CarrierInjective
set_option autoImplicit false
namespace NND_Carrier
def poolIdentity (x : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : RSL.PoolIdentity :=
 { pool := key x.pool,
   asset_mint := key x.asset_mint,
   token_program := key x.token_program,
   asset_id := word x.asset_id,
   deployment_domain := key x.deployment_domain }
theorem poolIdentity_injective : Function.Injective poolIdentity := by
 intro x y h
 cases x
 cases y
 simp only [poolIdentity,RSL.PoolIdentity.mk.injEq,key_eq_iff,word_eq_iff] at h
 simpa only [AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1.mk.injEq] using h
@[simp] theorem poolIdentity_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : poolIdentity x = poolIdentity y ↔ x = y :=
 ⟨fun h => poolIdentity_injective h,congrArg poolIdentity⟩
#print axioms poolIdentity_injective
#print axioms poolIdentity_eq_iff
end NND_Carrier
