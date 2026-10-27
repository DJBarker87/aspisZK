import ActualBeginSelectedCanonical
import FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_BeginCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Actual begin challenge canonicality, on the installed arithmetic carrier. -/
theorem value {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (before after : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges)
    (run : r1_wire.begin D pre before=ok (.Ok c,after)) :
    FIp_SemanticValues.Canon c.lambda ∧ FIp_SemanticValues.Canon c.chi ∧
    FIp_SemanticValues.Canon c.theta ∧ FIp_SemanticValues.Canon c.mu ∧
    FIp_SemanticValues.Canon c.eta ∧ ∀ x∈c.zc.val,FIp_SemanticValues.Canon x := by
  obtain ⟨hl,hc,ht,hm,he,hz⟩:=ActualBeginSelectedCanonical.begin_challenges_selected_canonical D pre before after c run
  refine ⟨hl,hc,ht,hm,he,?_⟩
  intro x mem
  obtain ⟨i,hi,hx⟩:=List.mem_iff_getElem.mp mem
  rw [←hx]
  exact hz ⟨i,by simpa only [c.zc.property] using hi⟩
#print axioms value
end AspisR1.FJn_BeginCanonical
end
