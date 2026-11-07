import NNH_MRegistryEntry1Check
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryEntry1Value
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 NNH_MRegistryEntry1Check.check (NNH_MRegistryOps.install base D env) v m.key e t entry expected =
 ok (if !decide (e.key = expected) || NNH_MEntryRecordGuards.bad1 v m entry t
     then .Err .InvalidAccountData else .Ok ()) := by
 simp only [NNH_MRegistryEntry1Check.check,NNH_MRegistryStd.key_ne,
  NNH_MRegistryScalarOps.to_bytes,NNH_MRegistryScalarOps.version,NNH_MRegistryScalarOps.active1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
  NNH_MEntryRecordGuards.bad1,NND_BoolReject.not_guard]
 exact (NND_BoolReject.eight _ _ _ _ _ _ _ _ _ _).trans (by split <;> rfl)

#print axioms value
end NNH_MRegistryEntry1Value
end
