import NLW_Full064State
set_option autoImplicit false
noncomputable section
namespace NLW_Full064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Complete nested law is delegated intact. In the stopped arm it retains
the ideal source reply/suffix and the actual pending prefix separately. -/
def Law (H : Bytes → State) {X : Type} (a : Args X) : End H a → Prop
 | .parseFail e=>NLE_ParseInstall.parse a.proof=.fail e
 | .parseDiv=>NLE_ParseInstall.parse a.proof=.div
 | .parseReject e=>NLE_ParseInstall.parse a.proof=.ok (.Err e)
 | .common outcome=>NLT_CompleteRoot.Law H a.digest a.publicBytes a.proof a.checkpoint a.hash outcome

def chronology {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (outcome : End H s.args) : List (Event Ambient X) :=
 let parsed:=NLE_ParseInstall.parse s.args.proof
 match outcome with
 | .common _=>[.parse s parsed,.marker s,.commonEnter s]
 | _=>[.parse s parsed]
#print Law
#print chronology
#print NLT_CompleteRoot.StoppedLaw
end NLW_Full064
