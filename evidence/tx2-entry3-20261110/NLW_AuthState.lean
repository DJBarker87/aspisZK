import NLW_Root0
import NLM_PacketTypes
set_option autoImplicit false
noncomputable section
namespace NLW_AuthState
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes
abbrev Reply := NLM_RowSpec_065.Reply
abbrev Args := NLM_RowSpec_065.Frame
/-- Native parent prestate: original immutable views and the complete
caller frame. No descriptor/token/buffer is selected again at a cut. -/
structure State (Ambient H : Type) where
 args : Args H
 world : World Ambient
inductive Event (Ambient H : Type) where
 | parse (before : State Ambient H)
   (reply : Result (core.result.Result transport.Variant verifier.Error))
 | parsed (before : State Ambient H)
 | common (before : State Ambient H)
   (reply : Observation Ambient NJU_CommonObserved.Event Reply)
abbrev Child (Ambient : Type) := NLM_RowSpec_065.Native Ambient
/-- Source-projection packet; Root0 is an OWN input clause. Internal
allocator/owned-buffer effects and native interpretation are absent, so this
is NOT the full-strength RowSpec_065 required by (be)/(bg). -/
def SourceSpec_065 {Ambient : Type} (child : Child Ambient)
 (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle)
 (finish : NJJ_Common.Finish) : Prop :=
 ∀ {H : Type} (args : Args H) (world : World Ambient), NLW_Root0.Domain args →
 child args world = ⟨world,NJU_CommonObserved.run wr rr merkle finish args.digest
  args.publicBytes args.proof args.checkpoint args.hash none⟩ ∧
 (child args world).run.result = NJJ_Common.run wr rr merkle finish args.digest
  args.publicBytes args.proof args.checkpoint args.hash none
/-- Line 1 parse, line 2 release marker, line 3 exact forwarding. All
outer errors and divergence stop at the reached prefix. -/
def transcription {Ambient H : Type} (child : Child Ambient) (s : State Ambient H) :
 Observation Ambient (Event Ambient H) Reply :=
 let p := NLE_ParseInstall.parse s.args.proof
 let e := Event.parse s p
 match p with
 | .fail err => ⟨s.world,⟨.fail err,[e]⟩⟩
 | .div => ⟨s.world,⟨.div,[e]⟩⟩
 | .ok (.Err err) => ⟨s.world,⟨.ok (.Err err),[e]⟩⟩
 | .ok (.Ok _) =>
   let c := child s.args s.world
   ⟨c.post,⟨c.run.result,[e,.parsed s,.common s c]⟩⟩
#print SourceSpec_065
#print transcription
end NLW_AuthState
