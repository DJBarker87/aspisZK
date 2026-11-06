import VTop_Model
import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NLE_Auth
open Aeneas Aeneas.Std Result VTop_Stages
def tryR {E A B : Type} {M : Type → Type} [Monad M]
 (reply : core.result.Result A E) (next : A → M (core.result.Result B E)) : M (core.result.Result B E) :=
 match reply with | .Ok a => next a | .Err e => pure (.Err e)
abbrev Reply := core.result.Result Unit verifier.Error
structure Frame (H : Type) where
 digest : aspis_core.digest.Digest32 H
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
 hash : H
 observer : Option (verifier.Phase → Result Unit)
inductive Event (H : Type) where
 | parse (proof : Slice U8) (reply : Result (core.result.Result transport.Variant verifier.Error))
 | mark (observer : Option (verifier.Phase → Result Unit)) (reply : Result Unit)
 | common (frame : Frame H) (reply : Result Reply)
structure State (H : Type) where
 frame : Frame H
 parsed : Option transport.Variant := none
 history : List (Event H) := []
abbrev Run (H A : Type) := NJU_Log.Run (Event H) A
/-- Parameterized child interface only; no root or credit while TX2:065 is OPEN. -/
abbrev Common (H : Type) := Frame H → Result Reply
def parse {H : Type} (ops : Ops) (s : State H) : Run H (core.result.Result (State H) verifier.Error) := do
 let reply ← NJU_Log.record (.parse s.frame.proof) (ops.op3 s.frame.proof)
 tryR reply fun variant =>
 pure (.Ok {s with parsed := some variant})
def mark {H : Type} (ops : Ops) (s : State H) : Run H (State H) := do
 let _ ← NJU_Log.record (.mark s.frame.observer) (ops.op13 s.frame.observer .Parsed)
 pure s
def common {H : Type} (child : Common H) (s : State H) : Run H Reply :=
 NJU_Log.record (.common s.frame) (child s.frame)
def G {H : Type} (ops : Ops) (child : Common H) (s : State H) : Run H Reply := do
 let reply ← parse ops s
 tryR reply fun post => do
 let next ← mark ops post
 common child next
/-- The exact source body with OPEN common as its sole continuation parameter. -/
def source {H : Type} (ops : Ops) (child : Common H) (s : State H) : Result Reply := do
 let reply ← ops.op3 s.frame.proof
 tryR reply fun _ => do
 let _ ← ops.op13 s.frame.observer .Parsed
 child s.frame
#print G
end NLE_Auth
