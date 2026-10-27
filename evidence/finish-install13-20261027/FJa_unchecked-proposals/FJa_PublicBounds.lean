import FJa_PublicCopy
import FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicBounds
open Aeneas Aeneas.Std Result
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open AspisR1TerminalDigestBindingCandidate.SemanticPublicFieldsCanonical
abbrev P := FIw_ScalarArithmetic.P
def digest (d : Array U32 8#usize) : Prop := ∀ x∈d.val,x.val<P
def frontier (d : Array (Array U32 8#usize) 20#usize) : Prop := ∀ row∈d.val,digest row
/-- The exact bounds required by FIz_SameComposition, on the installed public. -/
def Bounds (p : FJa_PublicCopy.Public) : Prop :=
  digest p.anchor ∧ digest p.nullifier ∧ digest p.change ∧
  (∀ r,p.recipient=some r → digest r) ∧
  frontier p.transition.live_snapshot.frontier ∧
  digest p.transition.candidate_afterstate.next_root ∧
  frontier p.transition.candidate_afterstate.next_frontier ∧
  p.asset_id.val<P ∧ (p.withdrawal_amount.getD 0#u32).val<P
/-- Reindex the retained per-cell bounds to the literal native list cells. -/
theorem digest_members (d : Array U32 8#usize) (h : digestValuesCanonical d) : digest d := by
  intro x hx
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hx' := h ⟨i,by simpa only [d.property] using hi⟩
  change (d.val[i]'hi).val < RetainedFieldByteCodec.m31Modulus at hx'
  rw [he] at hx'
  exact hx'
theorem frontier_members (d : Array (Array U32 8#usize) 20#usize)
    (h : frontierValuesCanonical d) : frontier d := by
  intro row hr
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
  apply digest_members
  subst row
  intro j
  exact h ⟨i,by simpa only [d.property] using hi⟩ j
/-- Native bounds are DERIVED from the retained checked preparation, with no
bounds premise at the installed terminal interface. -/
theorem from_copy (p : SemanticPublic) (h : copiedFieldsCanonical p) :
    Bounds (FJa_PublicCopy.native p) := by
  obtain ⟨ha,hn,hab,hc,hf,hnr,hnf,hr,haw⟩ := h
  refine ⟨digest_members _ ha,digest_members _ hn,digest_members _ hc,?_,
    frontier_members _ hf,digest_members _ hnr,frontier_members _ hnf,hab,?_⟩
  · intro r same
    exact digest_members r (hr r same)
  · cases hm : p.withdrawal_amount with
    | none => change (0#u32).val<P; decide
    | some amount => exact haw amount hm
#print axioms digest_members
#print axioms frontier_members
#print axioms from_copy
end AspisR1.FJa_PublicBounds
end
