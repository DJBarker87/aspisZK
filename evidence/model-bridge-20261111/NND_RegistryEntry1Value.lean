import NND_RegistryEntry1Check
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_RegistryEntry1Value
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 NND_RegistryEntry1Check.check (NND_RegistryOps.install base D env) v m.key e t entry expected =
 ok (if !decide (e.key = expected) || NND_EntryRecordGuards.bad1 v m entry t
     then .Err .InvalidAccountData else .Ok ()) := by
 simp only [NND_RegistryEntry1Check.check,NND_RegistryStd.key_ne,
  NND_RegistryScalarOps.to_bytes,NND_RegistryScalarOps.version,NND_RegistryScalarOps.active1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
  NND_EntryRecordGuards.bad1,NND_BoolReject.not_guard]
 exact (NND_BoolReject.eight _ _ _ _ _ _ _ _ _ _).trans (by split <;> rfl)

#print axioms value
end NND_RegistryEntry1Value
end
