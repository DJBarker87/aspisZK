import NLW_AuthFold
import NLE_AuthFold
set_option autoImplicit false
noncomputable section
namespace NLW_AuthModel
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- Exact nominal argument conversion; no new slice or hash is selected. -/
def frame {H : Type} (a : Args H) : NLE_Auth.Frame H :=
 ⟨a.digest,a.publicBytes,a.proof,a.checkpoint,a.hash,none⟩
def args {H : Type} (f : NLE_Auth.Frame H) : Args H :=
 ⟨f.digest,f.publicBytes,f.proof,f.checkpoint,f.hash⟩
def project {Ambient H : Type} (child : Child Ambient) (world : World Ambient) :
 NLE_Auth.Common H := fun f=>(child (args f) world).run.result
/-- Equality with the adopted source body with parser and marker installed.
Only the common continuation remains a parameter; this is not native closure. -/
theorem source {Ambient H : Type} (ops : Ops) (child : Child Ambient)
 (s : State Ambient H) : (NLW_AuthSegments.fold child s).run.result=
 NLE_Auth.source (NLE_AuthScope.install ops) (project child s.world)
  ⟨frame s.args,none,[]⟩ := by
 rw [NLW_AuthFold.transcription]
 unfold NLW_AuthState.transcription NLE_Auth.source
 dsimp only [NLE_AuthScope.install,NLE_ParseInstall.install,frame]
 cases p : NLE_ParseInstall.parse s.args.proof with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
#print frame
#print source
#print axioms source
end NLW_AuthModel
