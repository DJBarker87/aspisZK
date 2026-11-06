import NLW_AuthSegments
set_option autoImplicit false
noncomputable section
namespace NLW_AuthFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- Fold-first segment composition, complete in all Result arms. This is a
model equality until actual native contracts install the segment effects. -/
theorem transcription {Ambient H : Type} (child : Child Ambient) (s : State Ambient H) :
 NLW_AuthSegments.fold child s=NLW_AuthState.transcription child s := by
 unfold NLW_AuthSegments.fold NLW_AuthState.transcription
 cases p : NLE_ParseInstall.parse s.args.proof with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
/-- The exact own-input child domain at the only common call. Proof size is
from CLOSED parse; public extent and Root0 remain caller clauses. -/
theorem common_domain {Ambient H : Type} (s : State Ambient H) (v : transport.Variant)
 (parsed : NLE_ParseInstall.parse s.args.proof=.ok (.Ok v))
 (publicBound : s.args.publicBytes.val.length≤1880)
 (roots : NLW_Root0.Binds s.args.checkpoint s.args.proof) : NLW_Root0.Domain s.args :=
 ⟨⟨(NLE_ParseInstall.success s.args.proof v parsed).2,publicBound⟩,roots⟩
#print transcription
#print common_domain
#print axioms transcription
#print axioms common_domain
end NLW_AuthFold
