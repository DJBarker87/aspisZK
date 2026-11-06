import NKE_Free
set_option autoImplicit false
noncomputable section
namespace NKE_FreeReplay
open Aeneas Aeneas.Std Result NKE_Free
/-- A live state retains the ENTIRE caller continuation, including all fields
outside the callee footprint. No independent caller post-state is supplied. -/
inductive State (E A : Type) : Type 1 where
 | live (caller : Program E A) (remaining : List E)
 | done (result : Result A) (remaining : List E)
 | invalid

/-- Native G reads arbitrary full replies at the SAME decoded arguments.
The child model seed is deliberately ignored at every call node. -/
def G {E A : Type} (p : Program E A) (log : List E) : State E A :=
 match p with
 | .ret value => .done (.ok value) log
 | .prim actual next =>
   match actual with
   | .ok value => G (next value) log
   | .fail err => .done (.fail err) log
   | .div => .done .div log
 | .call codec _ next =>
   match log with
   | [] => .invalid
   | event::tail =>
     match codec.decode event with
     | none => .invalid
     | some (.ok value) => G (next value) tail
     | some (.fail err) => .done (.fail err) tail
     | some .div => .done .div tail
 termination_by structural p

/-- The same proof applies to EVERY oracle reply, including Rust Err values
and abort/divergence. The seed cannot hide the desired child endpoint. -/
theorem seed_unused {E A B : Type} (codec : Codec E B) (first second : Result B)
 (next : B → Program E A) (log : List E) :
 G (.call codec first next) log=G (.call codec second next) log := by
 cases log <;> simp only [G]

/-- Forward substitution at the actual source arguments. This is NOT an
inverse association of an independently selected native log. -/
theorem source {E A : Type} (p : Program E A) :
 G p (eval p).events=.done (eval p).result [] := by
 induction p with
 | ret value => rfl
 | prim actual next ih =>
  cases actual with
  | fail err => rfl
  | div => rfl
  | ok value => exact ih value
 | call codec actual next ih =>
  cases actual with
  | fail err => simp only [eval,G,codec.roundtrip]
  | div => simp only [eval,G,codec.roundtrip]
  | ok value =>
   simpa only [eval,G,codec.roundtrip] using ih value

/-- Stop after n entered child events, eagerly evaluating only literal std
operations. Err/abort prefixes terminate at their actual event. -/
def advance {E A : Type} (n : Nat) (p : Program E A) (log : List E) : State E A :=
 match p with
 | .ret value => .done (.ok value) log
 | .prim actual next =>
   match actual with
   | .ok value => advance n (next value) log
   | .fail err => .done (.fail err) log
   | .div => .done .div log
 | .call codec actual next =>
   match n with
   | 0 => .live (.call codec actual next) log
   | n+1 =>
     match log with
     | [] => .invalid
     | event::tail =>
       match codec.decode event with
       | none => .invalid
       | some (.ok value) => advance n (next value) tail
       | some (.fail err) => .done (.fail err) tail
       | some .div => .done .div tail
 termination_by structural p

/-- Source continuation after the SAME n events; no endpoint is a hypothesis. -/
def sourcePrefix {E A : Type} (n : Nat) (p : Program E A) : State E A :=
 match p with
 | .ret value => .done (.ok value) []
 | .prim actual next =>
   match actual with
   | .ok value => sourcePrefix n (next value)
   | .fail err => .done (.fail err) []
   | .div => .done .div []
 | .call codec actual next =>
   match n with
   | 0 => .live (.call codec actual next) (eval (.call codec actual next)).events
   | n+1 =>
     match actual with
     | .ok value => sourcePrefix n (next value)
     | .fail err => .done (.fail err) []
     | .div => .done .div []
 termination_by structural p

/-- Prefix induction carries the full caller frame, not only returned cells.
Concrete caller and codec instantiation is required before native credit. -/
theorem prefixes {E A : Type} (p : Program E A) (n : Nat) :
 advance n p (eval p).events=sourcePrefix n p := by
 induction p generalizing n with
 | ret value => rfl
 | prim actual next ih =>
  cases actual with
  | fail err => rfl
  | div => rfl
  | ok value => exact ih value n
 | call codec actual next ih =>
  cases n with
  | zero => rfl
  | succ n =>
   cases actual with
   | fail err => simp only [advance,sourcePrefix,eval,codec.roundtrip]
   | div => simp only [advance,sourcePrefix,eval,codec.roundtrip]
   | ok value =>
    simpa only [advance,sourcePrefix,eval,codec.roundtrip] using ih value n

#print axioms seed_unused
#print axioms source
#print axioms prefixes
end NKE_FreeReplay
