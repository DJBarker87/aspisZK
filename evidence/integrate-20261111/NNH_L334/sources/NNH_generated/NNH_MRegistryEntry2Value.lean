import NNH_MRegistryEntry2Check
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryEntry2Value
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (expected : solana_pubkey.Pubkey) :
 NNH_MRegistryEntry2Check.check (NNH_MRegistryOps.install base D env) v m.key t
  (unkey RSL.LOADER_ID) entry expected =
 ok (if NNH_MEntryV2Guard.bad v m entry t expected
     then .Err .InvalidAccountData else .Ok ()) := by
 simp only [NNH_MRegistryEntry2Check.check,NNH_MRegistryScalarOps.to_bytes,
  NNH_MRegistryScalarOps.version,NNH_MRegistryScalarOps.active2,NGL_ArrayEquality.ne_value,
  bind_tc_ok,NNH_MEntryV2Guard.bad,NND_BoolReject.not_guard]
 exact (NND_BoolReject.ten _ _ _ _ _ _ _ _ _ _ _ _).trans (by split <;> rfl)

#print axioms value
end NNH_MRegistryEntry2Value
end
