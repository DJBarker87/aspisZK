import NLW_AuthFold
set_option autoImplicit false
noncomputable section
namespace NLW_AuthPrefixes
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- Rejecting the parser retains precisely the attempted call prefix and
complete original state. There is no marker, allocation, loan or child suffix. -/
theorem reject {Ambient H : Type} (child : Child Ambient) (s : State Ambient H)
 (err : verifier.Error) (h : NLE_ParseInstall.parse s.args.proof=.ok (.Err err)) :
 NLW_AuthSegments.fold child s=
 ⟨s.world,⟨.ok (.Err err),[.parse s (.ok (.Err err))]⟩⟩ := by
 rw [NLW_AuthFold.transcription]
 simp only [NLW_AuthState.transcription,h]
theorem abort {Ambient H : Type} (child : Child Ambient) (s : State Ambient H)
 (err : Aeneas.Std.Error) (h : NLE_ParseInstall.parse s.args.proof=.fail err) :
 NLW_AuthSegments.fold child s=⟨s.world,⟨.fail err,[.parse s (.fail err)]⟩⟩ := by
 rw [NLW_AuthFold.transcription]
 simp only [NLW_AuthState.transcription,h]
theorem diverge {Ambient H : Type} (child : Child Ambient) (s : State Ambient H)
 (h : NLE_ParseInstall.parse s.args.proof=.div) :
 NLW_AuthSegments.fold child s=⟨s.world,⟨.div,[.parse s .div]⟩⟩ := by
 rw [NLW_AuthFold.transcription]
 simp only [NLW_AuthState.transcription,h]
#print reject
#print abort
#print diverge
#print axioms reject
#print axioms abort
#print axioms diverge
end NLW_AuthPrefixes
