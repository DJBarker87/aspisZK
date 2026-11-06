import NLJ_ControlStep
import NLJ_ObservedInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Log)
open NLJ_Observed
/-- ONE proposed native parent state/event chain. Fixed native-child bodies
appear in step; no source-equality clauses for CLOSED children are fields.
Each failed/divergent call retains its actual chronological log and stops.
Domain is the actual13831-byte prepare caller; physical byte-frame admission
is OPEN. This relation is a candidate cut TRANSCRIPTION, not proof that a
physical Rust run satisfies it. -/
inductive Invocation (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit) :
 Nat → NLJ_Observed.State Unit → Result (Out Unit) → Log → List Event → Input Unit → Prop where
 | returned {n : Nat} {s : State Unit} {out : Out Unit} {log : Log}
   (domain : s.input.bytes.val.length = 13831)
   (head : step native136 s = (log,.ok (.inl out))) :
   Invocation native136 (n+1) s (.ok out) log [event s] s.input
 | next {n : Nat} {s after : State Unit} {out : Result (Out Unit)}
   {log suffix : Log} {events : List Event} {last : Input Unit}
   (domain : s.input.bytes.val.length = 13831)
   (head : step native136 s = (log,.ok (.inr after)))
   (tail : Invocation native136 n after out suffix events last) :
   Invocation native136 (n+1) s out (log++suffix) (event s::events) last
 | fail {n : Nat} {s : State Unit} {error : Error} {log : Log}
   (domain : s.input.bytes.val.length = 13831)
   (head : step native136 s = (log,.fail error)) :
   Invocation native136 (n+1) s (.fail error) log [event s] s.input
 | div {n : Nat} {s : State Unit} {log : Log}
   (domain : s.input.bytes.val.length = 13831)
   (head : step native136 s = (log,.div)) :
   Invocation native136 (n+1) s .div log [event s] s.input
end AspisR1.NLJ_Control137
end
