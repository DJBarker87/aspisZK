import NKQ_ObservedTrace
import NLC_FinishState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Out (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
structure Input (H : Type) where
 reservation : NP6_StdModel.Reservation
 digest : aspis_core.Digest32 H
 publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public
 bytes : Slice U8
 hash : H
/-- Full carriers make uninitialized reads unrepresentable. -/
inductive Local (H : Type) where
 | parse
 | mark0 (prefix1 : r1_wire.Prefix)
 | publicTranscript (prefix1 : r1_wire.Prefix)
 | begin (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
 | mark1 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 | finish (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
inductive Event where
 | parse | mark0 | publicTranscript | begin | mark1 | finish
 deriving DecidableEq, Repr
structure State (H : Type) where
 input : Input H
 locals : Local H
abbrev Post (H : Type) := Sum (Out H) (State H)
def event {H : Type} (s : State H) : Event :=
 match s.locals with
 | .parse => .parse | .mark0 _ => .mark0 | .publicTranscript _ => .publicTranscript
 | .begin _ _ => .begin | .mark1 _ _ _ => .mark1 | .finish _ _ _ => .finish
def advance {H : Type} (s : State H) (l : Local H) : State H := {s with locals := l}
def Frame {H : Type} (s t : State H) : Prop := t.input = s.input
end AspisR1.NLJ_Observed
end
