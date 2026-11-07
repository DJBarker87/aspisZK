import NLW_AuthState
set_option autoImplicit false
noncomputable section
namespace NLW_AuthSegments
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLW_AuthState
/-- A local operational cut; every branch carries the same complete state.
No copying/allocation/borrow is performed by the parent between these calls. -/
inductive ParseCut (Ambient H : Type) where
 | aborted (err : Aeneas.Std.Error)
 | diverged
 | rejected (err : verifier.Error)
 | entered

def parse {Ambient H : Type} (_s : State Ambient H)
 (reply : Result (core.result.Result transport.Variant verifier.Error)) : ParseCut Ambient H :=
 match reply with
 | .fail err => .aborted err
 | .div => .diverged
 | .ok (.Err err) => .rejected err
 | .ok (.Ok _) => .entered
/-- The actual release marker is the literal None. It has no call,
allocation, SDK borrow or caller-frame effect. -/
def marker {Ambient H : Type} (s : State Ambient H) : State Ambient H := s
/-- The native common cut's input is the complete SAME original record.
Its complete post-state and nested child trace are returned unchanged. -/
def common {Ambient H : Type} (child : Child Ambient) (s : State Ambient H) :=
 child s.args s.world
/-- Explicit chronological fold. Early exits do not fabricate a later cut. -/
def fold {Ambient H : Type} (child : Child Ambient) (s : State Ambient H) :
 Observation Ambient (Event Ambient H) Reply :=
 let p := NLE_ParseInstall.parse s.args.proof
 let e := Event.parse s p
 match parse s p with
 | .aborted err => ⟨s.world,⟨.fail err,[e]⟩⟩
 | .diverged => ⟨s.world,⟨.div,[e]⟩⟩
 | .rejected err => ⟨s.world,⟨.ok (.Err err),[e]⟩⟩
 | .entered =>
   let next := marker s
   let c := common child next
   ⟨c.post,⟨c.run.result,[e,.parsed next,.common next c]⟩⟩
#print fold
end NLW_AuthSegments
