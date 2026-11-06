import NLM_RowSpec_065
import NLE_AuthLiteral
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes
abbrev Reply := NLM_RowSpec_065.Reply
structure Input (H : Type) where
 digest : aspis_core.digest.Digest32 H
 publicBytes : Array U8 1880#usize
 proof : Slice U8
 checkpoint : Slice U8
 hash : H
structure State (Ambient H : Type) where
 input : Input H
 world : World Ambient
 parsed : Option transport.Variant := none
inductive Event (Ambient H : Type) where
 | parse (before : State Ambient H) (reply : Result (core.result.Result transport.Variant verifier.Error))
 | mark (before : State Ambient H) (reply : Result Unit)
 | common (before : State Ambient H)
   (child : Observation Ambient NJU_CommonObserved.Event Reply)
def commonFrame {Ambient H : Type} (s : State Ambient H) : NLM_RowSpec_065.Frame H :=
 ⟨s.input.digest,s.input.publicBytes.to_slice,s.input.proof,s.input.checkpoint,s.input.hash⟩
/-- One native-parent state and one event family. Every child observation is
retained in full; errors/aborts never manufacture an independently chosen
successor. Release marker is the deployed literal None, not a pointer test. -/
def G {Ambient H : Type} (common : NLM_RowSpec_065.Native Ambient) (s : State Ambient H) :
 Observation Ambient (Event Ambient H) Reply :=
 let parsed := NLE_ParseInstall.parse s.input.proof
 let e := Event.parse s parsed
 match parsed with
 | .fail err => ⟨s.world,⟨.fail err,[e]⟩⟩
 | .div => ⟨s.world,⟨.div,[e]⟩⟩
 | .ok (.Err err) => ⟨s.world,⟨.ok (.Err err),[e]⟩⟩
 | .ok (.Ok variant) =>
   let post := {s with parsed:=some variant}
   let marker := NHV_ReleaseOps.mark none .Parsed
   let child := common (commonFrame post) post.world
   ⟨child.post,⟨child.run.result,[e,.mark post marker,.common post child]⟩⟩
#print G
end NLM_Auth064
