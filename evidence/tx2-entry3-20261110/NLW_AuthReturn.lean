import NLW_AuthFold
set_option autoImplicit false
noncomputable section
namespace NLW_AuthReturn
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- Common's full post and Result, including its abort prefix, are forwarded.
The parent's marker retains the exact state, not an independent seed. -/
theorem entered {Ambient H : Type} (child : Child Ambient) (s : State Ambient H)
 (v : transport.Variant) (h : NLE_ParseInstall.parse s.args.proof=.ok (.Ok v)) :
 NLW_AuthSegments.fold child s=
 ⟨(child s.args s.world).post,⟨(child s.args s.world).run.result,
 [.parse s (.ok (.Ok v)),.parsed s,.common s (child s.args s.world)]⟩⟩ := by
 rw [NLW_AuthFold.transcription]
 simp only [NLW_AuthState.transcription,h]
/-- Empty parent modifies between calls, universally in the entire SDK,
caller-owned ambient memory and return-data frame. This is a SOURCE law;
native representation/cut installation is a separate obligation. -/
theorem marker_frame {Ambient H : Type} (s : State Ambient H) :
 NLW_AuthSegments.marker s=s := rfl
#print entered
#print marker_frame
#print axioms entered
#print axioms marker_frame
end NLW_AuthReturn
