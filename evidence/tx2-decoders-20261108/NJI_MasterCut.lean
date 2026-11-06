import NJI_MasterModel
import NJI_StdAnyTransport
import NHY_ArrayExt
set_option autoImplicit false
noncomputable section
namespace NJI_MasterCut
open Aeneas Aeneas.Std Result NJI_MasterModel
attribute [local instance] Classical.propDecidable
abbrev P := NJI_PolicyPort.P
abbrev PF := NJI_PolicyPort.F

def Zero (m : M) : Prop :=
 m.identity.pool=Array.repeat 32#usize 0#u8 ∨
 m.identity.asset_mint=Array.repeat 32#usize 0#u8 ∨
 m.identity.token_program=Array.repeat 32#usize 0#u8 ∨
 m.identity.deployment_domain=Array.repeat 32#usize 0#u8

def PolicyCoordinates (p q : P) : Prop := p.flags=q.flags ∧ ∀ i, i<32 →
 NHY_ArrayExt.coord p.registry_program i=NHY_ArrayExt.coord q.registry_program i ∧
 NHY_ArrayExt.coord p.registry_authority i=NHY_ArrayExt.coord q.registry_authority i ∧
 NHY_ArrayExt.coord p.policy_binding i=NHY_ArrayExt.coord q.policy_binding i

theorem same_policy (p q : P) (h : PolicyCoordinates p q) : p=q := by
 have hp:=NHY_ArrayExt.whole p.registry_program q.registry_program (fun i hi _ => (h.2 i hi).1)
 have ha:=NHY_ArrayExt.whole p.registry_authority q.registry_authority (fun i hi _ => (h.2 i hi).2.1)
 have hb:=NHY_ArrayExt.whole p.policy_binding q.policy_binding (fun i hi _ => (h.2 i hi).2.2)
 cases p;cases q;simp_all [PolicyCoordinates]

def invalid (m : M) : Prop :=
 (¬m.has_checkpoint=true ∧ (m.next_checkpoint_sequence≠0#u64 ∨
   m.last_checkpoint_lane_sequences≠Array.repeat 8#usize 0#u64)) ∨
 (m.has_checkpoint=true ∧ m.next_checkpoint_sequence=0#u64)

/-- Literal K023/K024 parent-stage clauses. Callee replies are unrestricted;
logs identify the exact record/sequence passed before each entered call. -/
def Cut (m : M) (reply : core.result.Result Unit PF) (any : Bool)
 (plog : Option P) (slog : Option (Array U64 8#usize))
 (out : core.result.Result Unit F) : Prop :=
 if Zero m then plog=none ∧ slog=none ∧ out=.Err .ZeroRequiredBinding
 else ∃ p, plog=some p ∧ PolicyCoordinates p m.verifier_policy ∧
  match reply with
  | .Err _ => slog=none ∧ out=.Err .Policy
  | .Ok _ => (∃ s, slog=some s ∧ ∀ j, j<8 →
      NHY_ArrayExt.coord s j=NHY_ArrayExt.coord m.last_checkpoint_lane_sequences j) ∧
     if any=true ∨ invalid m then out=.Err .InvalidMasterState else out=.Ok ()

def closedReply (m : M) : core.result.Result Unit PF :=
 NJI_PolicyPort.unport (NHY_PolicyModel.decode
 (NHY_PolicyModel.code m.verifier_policy.flags
  (decide (m.verifier_policy.registry_program=Array.repeat 32#usize 0#u8))
  (decide (m.verifier_policy.registry_authority=Array.repeat 32#usize 0#u8))
  (decide (m.verifier_policy.policy_binding=Array.repeat 32#usize 0#u8))))

theorem policy_reply (m : M) : NJI_PolicyPort.validator m.verifier_policy=ok (closedReply m) :=
 NJI_PolicyPort.validator_value m.verifier_policy

/-- Both callee argument identifications are proved from native coordinates,
not supplied as same-input endpoint equations. -/
theorem child_arguments (m : M) (q : core.result.Result Unit PF) (a : Bool)
 (p : Option P) (s : Option (Array U64 8#usize)) (out : core.result.Result Unit F)
 (h : Cut m q a p s out) (entered : ¬Zero m) :
 p=some m.verifier_policy ∧ (∀ u, q=.Ok u → s=some m.last_checkpoint_lane_sequences) := by
 simp only [Cut,if_neg entered] at h
 obtain ⟨v,hp,hcoords,h⟩:=h
 have same:=same_policy v m.verifier_policy hcoords
 subst v
 refine ⟨hp,?_⟩
 intro u hq;subst q
 obtain ⟨⟨words,hs,hwords⟩,_⟩:=h
 have hw:=NHY_ArrayExt.whole words m.last_checkpoint_lane_sequences (fun j hj _ => hwords j hj)
 simpa [hw] using hs

theorem native_source (m : M) (p : Option P) (s : Option (Array U64 8#usize))
 (out : core.result.Result Unit F)
 (h : Cut m (closedReply m) (m.last_checkpoint_lane_sequences.val.any tooLarge) p s out) :
 ok out=raw m := by
 rw [source]
 unfold model
 rw [policy_reply]
 unfold Cut at h
 cases hq : closedReply m with
 | Err e =>
  simp only [hq] at h
  simp only [bind_tc_ok]
  by_cases hz : Zero m
  · simp only [if_pos hz] at h
    obtain ⟨_,_,hout⟩:=h
    rcases hz with hz|hz|hz|hz <;> simp_all
  · simp only [if_neg hz] at h
    obtain ⟨_,_,_,_,hout⟩:=h
    simp_all [Zero]
 | Ok u =>
  cases u
  simp only [hq] at h
  by_cases hz : Zero m
  · simp only [if_pos hz] at h
    obtain ⟨_,_,hout⟩:=h
    rcases hz with hz|hz|hz|hz <;> simp_all
  · simp only [if_neg hz] at h
    obtain ⟨_,_,_,_,hout⟩:=h
    simp only [bind_tc_ok]
    simp_all [Zero,invalid,terminal]
    split_ifs at hout ⊢ <;> simp_all
    all_goals aesop

#print native_source
#print axioms same_policy
#print axioms policy_reply
#print axioms child_arguments
#print axioms native_source
end NJI_MasterCut
