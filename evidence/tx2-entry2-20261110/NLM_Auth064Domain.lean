import NLM_Auth064State
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064
open Aeneas Aeneas.Std Result VTop_Stages NLM_PacketTypes
/-- Local branch fact from the SAME CLOSED parse invocation and actual
1880-byte encoder carrier. No native size or parser-success root premise. -/
theorem child_domain {Ambient H : Type} (s : State Ambient H) (variant : transport.Variant)
 (parsed : NLE_ParseInstall.parse s.input.proof=.ok (.Ok variant)) :
 NLM_RowSpec_065.Domain (commonFrame {s with parsed:=some variant}) := by
 exact ⟨(NLE_ParseInstall.success s.input.proof variant parsed).2,
  (NLE_Length.public_scope s.input.publicBytes).2⟩
#print child_domain
#print axioms child_domain
end NLM_Auth064
