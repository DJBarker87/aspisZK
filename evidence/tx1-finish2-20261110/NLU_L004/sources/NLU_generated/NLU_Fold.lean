import NLU_Action
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- A local NHZ-style fold for PreparedHashCode. Each head consumes the SAME
state and appends its chronological events; no suffix follows fail/div/Err.
This executable proposal is not a native cut theorem. -/
def fold {H : Type} : Nat → NLU.State H → Observation H
 | 0,s => ⟨s.machine.input,[],.fail .panic⟩
 | n+1,s =>
   let head := step s
   match head.reply with
   | .fail e => ⟨head.input,head.events,.fail e⟩
   | .div => ⟨head.input,head.events,.div⟩
   | .ok (.inl out) => ⟨head.input,head.events,.ok out⟩
   | .ok (.inr after) =>
     let tail := fold n after
     {tail with events:=head.events ++ tail.events}
/-- Typed invocation tree; an intermediate resource interpreter relation,
never a root premise asserting an independent native endpoint. -/
inductive Invocation {H : Type} : Nat → NLU.State H → Observation H → Prop where
 | zero (s : NLU.State H) : Invocation 0 s ⟨s.machine.input,[],.fail .panic⟩
 | done {n : Nat} {s : NLU.State H} {out : Returned H}
   (head : (step s).reply=.ok (.inl out)) :
   Invocation (n+1) s ⟨(step s).input,(step s).events,.ok out⟩
 | failed {n : Nat} {s : NLU.State H} {e : Error}
   (head : (step s).reply=.fail e) :
   Invocation (n+1) s ⟨(step s).input,(step s).events,.fail e⟩
 | diverged {n : Nat} {s : NLU.State H}
   (head : (step s).reply=.div) :
   Invocation (n+1) s ⟨(step s).input,(step s).events,.div⟩
 | next {n : Nat} {s after : NLU.State H} {out : Observation H}
   (head : (step s).reply=.ok (.inr after)) (tail : Invocation n after out) :
   Invocation (n+1) s {out with events:=(step s).events ++ out.events}
end AspisR1.NLU
end
