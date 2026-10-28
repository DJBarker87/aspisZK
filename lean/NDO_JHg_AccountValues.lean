import NDO_JHg_AuditDomains
import NDO_JHg_BindingsMaster
import NDO_JHg_Digest00
import NDO_JHg_Digest01
import NDO_JHg_Scalar00
import NDO_JHg_Scalar09
import NDO_JHg_Scalar18
import NDO_JHd_ScanValue
import JHf_Carrier14
set_option autoImplicit false
namespace AspisR1.JHg_AccountValues
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
/-- Expected corrected decoded values. No complete decoder or authentication
success is supplied by these structural inputs. -/
def domain : Array U8 32#usize :=
  ⟨(JHg_DataMaster.bytes.drop 176).take 32,by rw [JHg_AuditMaster.domain];decide⟩
def mint : Array U8 32#usize := Array.repeat 32#usize 66#u8
def token : Array U8 32#usize :=
  ⟨(JHg_DataMaster.bytes.drop 136).take 32,by rw [JHg_AuditMaster.token];decide⟩
def master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 :=
  {bump:=254#u8,identity:=⟨JFu_PublicBindings.pool,mint,token,77#u32,domain⟩,
   verifier_policy:=⟨3#u8,JHb_Programs.registry,Array.repeat 32#usize 0#u8,Array.repeat 32#usize 7#u8⟩,
   initialized_lane_mask:=255#u8,has_checkpoint:=true,
   next_checkpoint_sequence:=core.num.U64.from_le_bytes JHg_Scalar00.value,
   last_checkpoint_lane_sequences:=Array.repeat 8#usize 0#u64}
def checkpoint : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 :=
  {bump:=254#u8,master:=JFs_Cell00.value,deployment_domain:=domain,
   checkpoint_sequence:=core.num.U64.from_le_bytes JHg_Scalar09.value,
   global_root:=JFt_Digest00.value,lane_sequences:=Array.repeat 8#usize 0#u64}
def lane : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
  {bump:=255#u8,master:=JFs_Cell00.value,lane_id:=3#u8,
   tree:=⟨core.num.U64.from_le_bytes JHg_Scalar18.value,
     JFt_SnapshotValue.value.current_root,JFt_SnapshotValue.value.frontier⟩}
def live : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=JFu_PublicBindings.pool,deployment_domain:=master.identity.deployment_domain,
   sequence:=lane.tree.next_leaf_index,next_pair_index:=lane.tree.next_leaf_index,
   current_root:=lane.tree.root,frontier:=lane.tree.frontier}
def value : r1_pool_adapter.AuthenticatedAsq8Accounts :=
  {master_account:=JFs_Cell00.value,checkpoint_account:=JFs_Cell01.value,
   selected_lane_account:=JFs_Cell02.value,master:=master,checkpoint:=checkpoint,
   selected_lane:=lane,live_snapshot:=live}

theorem domain_target : domain=JFu_PublicBindings.domain :=
  Subtype.ext JHg_AuditDomains.target
#print axioms domain_target

theorem master_domain : value.master.identity.deployment_domain=JFu_PublicBindings.domain := domain_target
#print axioms master_domain

theorem live_domain : value.live_snapshot.deployment_domain=JFu_PublicBindings.domain := domain_target
#print axioms live_domain
end AspisR1.JHg_AccountValues
