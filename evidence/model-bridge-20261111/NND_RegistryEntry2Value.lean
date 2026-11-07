import NND_RegistryEntry2Check
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_RegistryEntry2Value
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (expected : solana_pubkey.Pubkey) :
 NND_RegistryEntry2Check.check (NND_RegistryOps.install base D env) v m.key t
  (unkey RSL.LOADER_ID) entry expected =
 ok (if NND_EntryV2Guard.bad v m entry t expected
     then .Err .InvalidAccountData else .Ok ()) := by
 simp only [NND_RegistryEntry2Check.check,NND_RegistryScalarOps.to_bytes,
  NND_RegistryScalarOps.version,NND_RegistryScalarOps.active2,NGL_ArrayEquality.ne_value,
  bind_tc_ok,NND_EntryV2Guard.bad,NND_BoolReject.not_guard]
 exact (NND_BoolReject.ten _ _ _ _ _ _ _ _ _ _ _ _).trans (by split <;> rfl)

#print axioms value
end NND_RegistryEntry2Value
end
