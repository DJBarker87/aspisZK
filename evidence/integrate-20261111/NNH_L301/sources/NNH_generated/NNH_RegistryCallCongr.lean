import NND_Registry
set_option autoImplicit false
noncomputable section
namespace NNH_RegistryCallCongr
open Aeneas Aeneas.Std AdapterRw
/-- Symbolic source-call congruence on exactly the reached slots. It does not
unfold a deployed SDK or require equality of unrelated dictionary fields. -/
theorem same (left right : Ops)
 (h13 : left.op13=right.op13)
 (h14 : left.op14=right.op14)
 (h15 : left.op15=right.op15)
 (h18 : left.op18=right.op18)
 (h25 : left.op25=right.op25)
 (h26 : left.op26=right.op26)
 (h27 : left.op27=right.op27)
 (h28 : left.op28=right.op28)
 (h29 : left.op29=right.op29)
 (h30 : left.op30=right.op30)
 (h31 : left.op31=right.op31)
 (h32 : left.op32=right.op32)
 (h33 : left.op33=right.op33)
 (h34 : left.op34=right.op34)
 (h35 : left.op35=right.op35)
 (h36 : left.op36=right.op36)
 (h37 : left.op37=right.op37)
 (h38 : left.op38=right.op38)
 (h39 : left.op39=right.op39)
 (h40 : left.op40=right.op40)
 (h41 : left.op41=right.op41)
 (h45 : left.op45=right.op45)
 (h46 : left.op46=right.op46)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 r1_pool_adapter.owned.authenticate_invariant_release_registry left v p m s reg ent t =
 r1_pool_adapter.owned.authenticate_invariant_release_registry right v p m s reg ent t := by
 cases left
 cases right
 cases h13
 cases h14
 cases h15
 cases h18
 cases h25
 cases h26
 cases h27
 cases h28
 cases h29
 cases h30
 cases h31
 cases h32
 cases h33
 cases h34
 cases h35
 cases h36
 cases h37
 cases h38
 cases h39
 cases h40
 cases h41
 cases h45
 cases h46
 rfl
#print axioms same
end NNH_RegistryCallCongr
