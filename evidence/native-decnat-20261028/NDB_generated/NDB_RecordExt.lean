import NCV_ArrayFrame
import NCV_Reference.Types
set_option autoImplicit false
namespace NDB_RecordExt
open Aeneas Aeneas.Std Result

theorem array {A : Type} [Inhabited A] {n : Usize} (a b : Array A n)
    (cells : ∀ j, j<n.val → NCV_ArrayFrame.coord a j=NCV_ArrayFrame.coord b j) : a=b := by
  apply NCV_ArrayFrame.whole
  intro j hj hn
  exact cells j hn

theorem identity (a b : NCV_Reference.Identity)
    (pool : ∀ j, j<32 → NCV_ArrayFrame.coord a.pool j=NCV_ArrayFrame.coord b.pool j)
    (mint : ∀ j, j<32 → NCV_ArrayFrame.coord a.asset_mint j=NCV_ArrayFrame.coord b.asset_mint j)
    (token : ∀ j, j<32 → NCV_ArrayFrame.coord a.token_program j=NCV_ArrayFrame.coord b.token_program j)
    (domain : ∀ j, j<32 → NCV_ArrayFrame.coord a.deployment_domain j=NCV_ArrayFrame.coord b.deployment_domain j)
    (asset : a.asset_id=b.asset_id) : a=b := by
  have p:=array a.pool b.pool pool
  have m:=array a.asset_mint b.asset_mint mint
  have t:=array a.token_program b.token_program token
  have d:=array a.deployment_domain b.deployment_domain domain
  cases a;cases b;simp_all

theorem policy (a b : NCV_Reference.Policy)
    (flags : a.flags=b.flags)
    (program : ∀ j, j<32 → NCV_ArrayFrame.coord a.registry_program j=NCV_ArrayFrame.coord b.registry_program j)
    (authority : ∀ j, j<32 → NCV_ArrayFrame.coord a.registry_authority j=NCV_ArrayFrame.coord b.registry_authority j)
    (binding : ∀ j, j<32 → NCV_ArrayFrame.coord a.policy_binding j=NCV_ArrayFrame.coord b.policy_binding j) : a=b := by
  have p:=array a.registry_program b.registry_program program
  have m:=array a.registry_authority b.registry_authority authority
  have t:=array a.policy_binding b.policy_binding binding
  cases a;cases b;simp_all

theorem master (a b : NCV_Reference.Master)
    (bump : a.bump=b.bump) (id : a.identity=b.identity)
    (policy : a.verifier_policy=b.verifier_policy)
    (mask : a.initialized_lane_mask=b.initialized_lane_mask)
    (has : a.has_checkpoint=b.has_checkpoint) (next : a.next_checkpoint_sequence=b.next_checkpoint_sequence)
    (seq : ∀ j, j<8 → NCV_ArrayFrame.coord a.last_checkpoint_lane_sequences j=
      NCV_ArrayFrame.coord b.last_checkpoint_lane_sequences j) : a=b := by
  have s:=array a.last_checkpoint_lane_sequences b.last_checkpoint_lane_sequences seq
  cases a;cases b;simp_all

theorem checkpoint (a b : NCV_Reference.Checkpoint)
    (bump : a.bump=b.bump) (seq : a.checkpoint_sequence=b.checkpoint_sequence)
    (master : ∀ j, j<32 → NCV_ArrayFrame.coord a.master j=NCV_ArrayFrame.coord b.master j)
    (domain : ∀ j, j<32 → NCV_ArrayFrame.coord a.deployment_domain j=NCV_ArrayFrame.coord b.deployment_domain j)
    (root : ∀ j, j<8 → NCV_ArrayFrame.coord a.global_root j=NCV_ArrayFrame.coord b.global_root j)
    (lanes : ∀ j, j<8 → NCV_ArrayFrame.coord a.lane_sequences j=NCV_ArrayFrame.coord b.lane_sequences j) : a=b := by
  have m:=array a.master b.master master
  have d:=array a.deployment_domain b.deployment_domain domain
  have r:=array a.global_root b.global_root root
  have l:=array a.lane_sequences b.lane_sequences lanes
  cases a;cases b;simp_all
#print axioms array
#print axioms identity
#print axioms policy
#print axioms master
#print axioms checkpoint
end NDB_RecordExt
