import RPu_FJa_PublicCopy
import RPu_FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicBounds
open Aeneas Aeneas.Std Result
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
theorem digest_raw (d : Array U32 8#usize)
    (h : ∀ i : Fin 8,PublicSourceRaw.fieldCanonical (AspisR1PublicSerializer.RawBridge431.projectDigest d i)) : digest d := by
  intro x hx
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hx' := h ⟨i,by simpa only [d.property,show (8#usize).val=8 from rfl] using hi⟩
  change (d.val[i]'hi).val < RetainedFieldByteCodec.m31Modulus at hx'
  rw [he] at hx'
  exact hx'
theorem frontier_raw (d : Array (Array U32 8#usize) 20#usize)
    (h : ∀ l : Fin 20,∀ i : Fin 8,PublicSourceRaw.fieldCanonical
      (AspisR1PublicSerializer.RawBridge431.projectFrontier d l i)) : frontier d := by
  intro row hr
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
  subst row
  apply digest_raw
  exact h ⟨i,by simpa only [d.property,show (20#usize).val=20 from rfl] using hi⟩
/-- Reuse the actual preparation's raw canonicality, deriving every native
bound by its literal carrier projection. -/
theorem from_raw (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (h : PublicSourceRaw.Canonical (AspisR1TerminalDecoder.PublicBinding.projectRaw s)) :
    Bounds (FJa_PublicCopy.native (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) := by
  cases s with
  | PrivateTransfer c p =>
    simp only [AspisR1TerminalDecoder.PublicBinding.projectRaw,
      AspisR1TerminalDecoder.PublicBinding.toSerializer,
      AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
      AspisR1PublicSerializer.RawBridge431.project,
      AspisR1PublicSerializer.RawBridge431.projectCommon,
      PublicRawCoreAgreement.fromCore,PublicRawCoreAgreement.fromCoreCommon,
      PublicSourceRaw.Canonical,PublicSourceRaw.commonCanonical] at h
    obtain ⟨⟨ha,hn,hab,hc,hf,hnr,hnf⟩,hr⟩ := h
    refine ⟨digest_raw _ ha,digest_raw _ hn,digest_raw _ hc,?_,frontier_raw _ hf,
      digest_raw _ hnr,frontier_raw _ hnf,hab,?_⟩
    · intro r same
      have eq : p.recipient_commitment=r := Option.some.inj same
      subst r
      exact digest_raw _ hr
    · change (0#u32).val<P
      decide
  | Withdrawal c p =>
    simp only [AspisR1TerminalDecoder.PublicBinding.projectRaw,
      AspisR1TerminalDecoder.PublicBinding.toSerializer,
      AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
      AspisR1PublicSerializer.RawBridge431.project,
      AspisR1PublicSerializer.RawBridge431.projectCommon,
      PublicRawCoreAgreement.fromCore,PublicRawCoreAgreement.fromCoreCommon,
      PublicSourceRaw.Canonical,PublicSourceRaw.commonCanonical] at h
    obtain ⟨⟨ha,hn,hab,hc,hf,hnr,hnf⟩,haw⟩ := h
    refine ⟨digest_raw _ ha,digest_raw _ hn,digest_raw _ hc,?_,frontier_raw _ hf,
      digest_raw _ hnr,frontier_raw _ hnf,hab,haw⟩
    · intro r same
      cases same
#print axioms digest_raw
#print axioms frontier_raw
#print axioms from_raw
end AspisR1.FJa_PublicBounds
end
