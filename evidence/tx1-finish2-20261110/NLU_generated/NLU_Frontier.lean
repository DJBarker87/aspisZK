import NLU_Invariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Frontier
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Last ENTERED parent state, retained even on abort. This is not an invented
post-state after a nonreturning child; the child's internal prefix is separate. -/
structure Observation (H : Type) where
 summary : NLU.Observation H
 frontier : NLU.State H
def run {H : Type} : Nat → NLU.State H → Observation H
 | 0,s=>⟨⟨s.machine.input,[],.fail .panic⟩,s⟩
 | n+1,s=>
   let head:=NLU.step s
   match head.reply with
   | .fail err=>⟨⟨head.input,head.events,.fail err⟩,s⟩
   | .div=>⟨⟨head.input,head.events,.div⟩,s⟩
   | .ok (.inl out)=>⟨⟨head.input,head.events,.ok out⟩,s⟩
   | .ok (.inr after)=>
     let tail:=run n after
     {tail with summary:={tail.summary with events:=head.events++tail.summary.events}}
/-- No independent execution is selected for the extended observation. -/
theorem summary {H : Type} (n : Nat) (s : NLU.State H) :
 (run n s).summary=NLU.fold n s := by
 induction n generalizing s with
 | zero=>rfl
 | succ n ih=>
   simp only [run,NLU.fold]
   cases h : (NLU.step s).reply with
   | fail err=>rfl
   | div=>rfl
   | ok post=>cases post with
     | inl out=>rfl
     | inr after=>simp only [ih]
/-- The same reachable-state invariant holds at every abort/return frontier.
It describes the prefix before the last entered occurrence, never the heap
post of an aborting child. -/
theorem reached {H : Type} (input : NLU.Input H) (n : Nat) (s : NLU.State H)
 (before : NLU.Reachable input s) : NLU.Reachable input (run n s).frontier := by
 induction n generalizing s with
 | zero=>exact before
 | succ n ih=>
   simp only [run]
   cases h : (NLU.step s).reply with
   | fail err=>exact before
   | div=>exact before
   | ok post=>cases post with
     | inl out=>exact before
     | inr after=>exact ih after (.next before h)
#print axioms summary
#print axioms reached
end AspisR1.NLU_Frontier
end
