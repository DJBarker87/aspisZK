import NKF_ArrayFrame
import NKF_BoxInstall
set_option autoImplicit false
noncomputable section
namespace NKF_BoxFields
open Aeneas Aeneas.Std Result
abbrev M := NJQ_Carrier.CM
abbrev C := NJQ_Carrier.CC
structure Master (a b : M) : Prop where
 bump : a.bump=b.bump
 pool : NKF_ArrayFrame.CellEq a.identity.pool b.identity.pool
 mint : NKF_ArrayFrame.CellEq a.identity.asset_mint b.identity.asset_mint
 token : NKF_ArrayFrame.CellEq a.identity.token_program b.identity.token_program
 asset : a.identity.asset_id=b.identity.asset_id
 domain : NKF_ArrayFrame.CellEq a.identity.deployment_domain b.identity.deployment_domain
 flags : a.verifier_policy.flags=b.verifier_policy.flags
 registry : NKF_ArrayFrame.CellEq a.verifier_policy.registry_program b.verifier_policy.registry_program
 authority : NKF_ArrayFrame.CellEq a.verifier_policy.registry_authority b.verifier_policy.registry_authority
 policy : NKF_ArrayFrame.CellEq a.verifier_policy.policy_binding b.verifier_policy.policy_binding
 mask : a.initialized_lane_mask=b.initialized_lane_mask
 checkpoint : a.has_checkpoint=b.has_checkpoint
 next : a.next_checkpoint_sequence=b.next_checkpoint_sequence
 lanes : NKF_ArrayFrame.CellEq a.last_checkpoint_lane_sequences b.last_checkpoint_lane_sequences

structure Checkpoint (a b : C) : Prop where
 bump : a.bump=b.bump
 master : NKF_ArrayFrame.CellEq a.master b.master
 domain : NKF_ArrayFrame.CellEq a.deployment_domain b.deployment_domain
 sequence : a.checkpoint_sequence=b.checkpoint_sequence
 root : NKF_ArrayFrame.CellEq a.global_root b.global_root
 lanes : NKF_ArrayFrame.CellEq a.lane_sequences b.lane_sequences

theorem master (a b : M) (cells : Master a b) : a=b := by
 have hp := NKF_ArrayFrame.array_ext _ _ cells.pool
 have hm := NKF_ArrayFrame.array_ext _ _ cells.mint
 have ht := NKF_ArrayFrame.array_ext _ _ cells.token
 have hd := NKF_ArrayFrame.array_ext _ _ cells.domain
 have hr := NKF_ArrayFrame.array_ext _ _ cells.registry
 have ha := NKF_ArrayFrame.array_ext _ _ cells.authority
 have hpb := NKF_ArrayFrame.array_ext _ _ cells.policy
 have hl := NKF_ArrayFrame.array_ext _ _ cells.lanes
 rcases a with ⟨ab,ai,ap,am,ac,an,al⟩
 rcases b with ⟨bb,bi,bp,bm,bc,bn,bl⟩
 rcases ai with ⟨aip,aim,ait,aia,aid⟩
 rcases bi with ⟨bip,bim,bit,bia,bid⟩
 rcases ap with ⟨apf,apr,apa,apb⟩
 rcases bp with ⟨bpf,bpr,bpa,bpb⟩
 have hab:=cells.bump;have has:=cells.asset;have hf:=cells.flags
 have hmask:=cells.mask;have hc:=cells.checkpoint;have hn:=cells.next
 simp only at hp hm ht hd hr ha hpb hl hab has hf hmask hc hn
 cases hab;cases hp;cases hm;cases ht;cases has;cases hd
 cases hf;cases hr;cases ha;cases hpb;cases hmask;cases hc;cases hn;cases hl
 rfl

theorem checkpoint (a b : C) (cells : Checkpoint a b) : a=b := by
 have hm := NKF_ArrayFrame.array_ext _ _ cells.master
 have hd := NKF_ArrayFrame.array_ext _ _ cells.domain
 have hr := NKF_ArrayFrame.array_ext _ _ cells.root
 have hl := NKF_ArrayFrame.array_ext _ _ cells.lanes
 rcases a with ⟨ab,am,ad,asq,ar,al⟩
 rcases b with ⟨bb,bm,bd,bsq,br,bl⟩
 have hb:=cells.bump;have hs:=cells.sequence
 simp only at hm hd hr hl hb hs
 cases hb;cases hm;cases hd;cases hs;cases hr;cases hl
 rfl
#print axioms master
#print axioms checkpoint
end NKF_BoxFields
