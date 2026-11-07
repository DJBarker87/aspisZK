import NND_AuthCarrier
set_option autoImplicit false
namespace NNH_AuthResult
open Aeneas Aeneas.Std AdapterRw NND_Carrier

def value (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1)
 (lane : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1)
 (m c l : solana_pubkey.Pubkey) : r1_pool_adapter.AuthenticatedAsq8Accounts :=
 {master_account:=m,checkpoint_account:=c,selected_lane_account:=l,master:=master,checkpoint:=ck,selected_lane:=lane,
  live_snapshot:={pool:=m,deployment_domain:=master.identity.deployment_domain,sequence:=lane.tree.next_leaf_index,next_pair_index:=lane.tree.next_leaf_index,current_root:=lane.tree.root,frontier:=lane.tree.frontier}}

theorem carrier (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1)
 (lane : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1)
 (m c l : solana_pubkey.Pubkey) :
 auth (value master ck lane m c l) = {master_account:=key m,checkpoint_account:=key c,selected_lane_account:=key l,master:=NND_Carrier.master master,checkpoint:=NND_Carrier.checkpoint ck,selected_lane:=NND_Carrier.lane lane,live_snapshot:={pool:=key m,deployment_domain:=(NND_Carrier.master master).identity.deployment_domain,sequence:=(NND_Carrier.lane lane).tree.next_leaf_index,next_pair_index:=(NND_Carrier.lane lane).tree.next_leaf_index,current_root:=(NND_Carrier.lane lane).tree.root,frontier:=(NND_Carrier.lane lane).tree.frontier}} := by rfl
#print axioms carrier
end NNH_AuthResult
