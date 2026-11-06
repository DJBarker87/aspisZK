import NKF_BoxFields
set_option autoImplicit false
noncomputable section
namespace NKF_Windows
open Aeneas Aeneas.Std Result

def Bounded {A : Type} {n : Usize} (a b : Array A n) : Prop :=
 ∀ i : Nat, i<n.val → a.val[i]?=b.val[i]?

def WordWindow {A : Type} (a b : Array A 8#usize) : Prop :=
 ∀ i : Nat, i<32 → a.val[i%8]?=b.val[i%8]?

theorem bounded_cells {A : Type} {n : Usize} (a b : Array A n)
 (windows : Bounded a b) : NKF_ArrayFrame.CellEq a b := by
 intro i
 by_cases inside : i<n.val
 · exact windows i inside
 · have ha := a.property
   have hb := b.property
   rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

theorem word_cells {A : Type} (a b : Array A 8#usize)
 (windows : WordWindow a b) : NKF_ArrayFrame.CellEq a b := by
 apply bounded_cells
 intro i inside
 have small : i<8 := inside
 have same := windows i (by omega)
 simpa only [Nat.mod_eq_of_lt small] using same

structure Master (a b : NJQ_Carrier.CM) : Prop where
 bump : a.bump=b.bump
 pool : Bounded a.identity.pool b.identity.pool
 mint : Bounded a.identity.asset_mint b.identity.asset_mint
 token : Bounded a.identity.token_program b.identity.token_program
 asset : a.identity.asset_id=b.identity.asset_id
 domain : Bounded a.identity.deployment_domain b.identity.deployment_domain
 flags : a.verifier_policy.flags=b.verifier_policy.flags
 registry : Bounded a.verifier_policy.registry_program b.verifier_policy.registry_program
 authority : Bounded a.verifier_policy.registry_authority b.verifier_policy.registry_authority
 policy : Bounded a.verifier_policy.policy_binding b.verifier_policy.policy_binding
 mask : a.initialized_lane_mask=b.initialized_lane_mask
 checkpoint : a.has_checkpoint=b.has_checkpoint
 next : a.next_checkpoint_sequence=b.next_checkpoint_sequence
 lanes : WordWindow a.last_checkpoint_lane_sequences b.last_checkpoint_lane_sequences

structure Checkpoint (a b : NJQ_Carrier.CC) : Prop where
 bump : a.bump=b.bump
 master : Bounded a.master b.master
 domain : Bounded a.deployment_domain b.deployment_domain
 sequence : a.checkpoint_sequence=b.checkpoint_sequence
 root : WordWindow a.global_root b.global_root
 lanes : WordWindow a.lane_sequences b.lane_sequences

theorem master_fields (a b : NJQ_Carrier.CM) (windows : Master a b) :
 NKF_BoxFields.Master a b :=
 ⟨windows.bump,bounded_cells _ _ windows.pool,bounded_cells _ _ windows.mint,
 bounded_cells _ _ windows.token,windows.asset,bounded_cells _ _ windows.domain,
 windows.flags,bounded_cells _ _ windows.registry,bounded_cells _ _ windows.authority,
 bounded_cells _ _ windows.policy,windows.mask,windows.checkpoint,windows.next,
 word_cells _ _ windows.lanes⟩

theorem checkpoint_fields (a b : NJQ_Carrier.CC) (windows : Checkpoint a b) :
 NKF_BoxFields.Checkpoint a b :=
 ⟨windows.bump,bounded_cells _ _ windows.master,bounded_cells _ _ windows.domain,
 windows.sequence,word_cells _ _ windows.root,word_cells _ _ windows.lanes⟩

set_option pp.proofs false in
#print bounded_cells
#print axioms bounded_cells
#print axioms word_cells
#print axioms master_fields
#print axioms checkpoint_fields
end NKF_Windows
