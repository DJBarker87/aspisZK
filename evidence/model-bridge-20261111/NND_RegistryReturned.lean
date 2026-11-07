import NND_RegistryFullValue
import NND_ResultProjection
set_option autoImplicit false
noncomputable section
namespace NND_RegistryReturned
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NND_RegistryOps.install base D env) v p m s r e t =
 ok (unreply id (NND_RegistryEval.value (NND_RegistryLibrary.install L) D (NND_RegistryArgs.args v p m s r e t) env)) :=
 NND_ResultProjection.program_ok _ _ (NND_RegistryFullValue.value base L D env v p m s r e t)

/-- Both Ok and Err at exactly the RSL observation's oracle environment. This
is the complete 234 local bridge. It does not claim that RegistryOps.install
is the final DrvC sdk; that installation remains an A2 obligation. -/
theorem returned (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (o : RSL.Obs (Except RSL.ProgramError Unit)) (r : Except RSL.ProgramError Unit)
 (hr : RSL.TX2_234.Ref (NND_RegistryLibrary.install L) D (NND_RegistryArgs.args v p m s reg ent t) env o)
 (he : o.exit = .ret r) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry (NND_RegistryOps.install base D env) v p m s reg ent t =
 ok (unreply id r) := by
 have h := NND_RegistryEval.returned (NND_RegistryLibrary.install L) D (NND_RegistryArgs.args v p m s reg ent t) env o r hr he
 rw [h]
 exact value base L D env v p m s reg ent t

#print axioms value
#print axioms returned
end NND_RegistryReturned
end
