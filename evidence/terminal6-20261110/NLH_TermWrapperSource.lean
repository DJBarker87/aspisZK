import NLH_TermPartsSource
import NLH_TermWrapperFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermWrapperSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal
abbrev Public := r0.Public
abbrev Challenges := state_only_prefix.r0.Challenges

def validated (pub : Public) (out : NQ) := do
 let result←validate_transition (NKR_TermPublic.value pub)
 match result with
 | .Err _=>ok (core.result.Result.Err state_only_prefix.r0.Error.Public)
 | .Ok _=>ok (.Ok out)

/-- Complete256 EMITTED-source composition on arbitrary3x29claims/public.
The actual selected84,semantic255,parts263,and everymap/errorarm are derived
internally. SOURCE SUPPORT ONLY: missingnative237/256windows and218/261
composition cannot be replaced by this theorem or a source-only packet. -/
theorem source (pub : Public) (claims : NLH_TermSelected.Claims)
 (point : Array NQ 10#usize) (c : Challenges)
 (hd : NKR_DigestChildren.Domain (NKR_TermPublic.value pub))
 (hc : ∀ row∈claims.val,canonical row) (hp : canonical point) (hz : canonical c.zc)
 (hl : Canon c.lambda) (hchi : Canon c.chi) (ht : Canon c.theta) (hm : Canon c.mu)
 (asset : (NKR_TermPublic.value pub).asset_id.val<2147483647) :
 r0.Public.terminal_qm31 pub claims point c=ok (.Err .Public) ∨
 ∃ out,r0.Public.terminal_qm31 pub claims point c=validated pub out ∧ Canon out := by
 obtain ⟨selected,gather,cs,wrapper⟩:=NLH_TermWrapperFactor.source pub claims point c hc
 rcases NLH_TermPartsSource.source (NKR_TermPublic.value pub) selected point c.zc c.lambda c.chi c.theta c.mu hd cs hp hz hl hchi ht hm asset with rejected|accepted
 · rcases rejected with ⟨_,parts⟩
   left
   rw [wrapper]
   unfold NLH_TermWrapperFactor.reference
   rw [parts,bind_tc_ok]
   rfl
 · rcases accepted with ⟨parts,_,partsCall,co,_,_,_⟩
   refine Or.inr ⟨parts.1,?_,co⟩
   rw [wrapper]
   unfold NLH_TermWrapperFactor.reference
   rw [partsCall]
   unfold NLH_TermPartsSource.validated validated
   cases result : validate_transition (NKR_TermPublic.value pub) with
   | fail e=>rfl
   | div=>rfl
   | ok value=>cases value <;> rfl
#print source
#print axioms source
end AspisR1.NLH_TermWrapperSource
end
