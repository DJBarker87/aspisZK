import NJU_Log
set_option autoImplicit false
namespace NKK_LogClauses
open Aeneas Aeneas.Std

def Holds {E A : Type} (p : E → Prop) (m : NJU_Log.Run E A) : Prop :=
 List.Forall p m.events

theorem pure {E A : Type} (p : E → Prop) (a : A) :
 Holds p (Pure.pure a : NJU_Log.Run E A) := List.Forall.nil

theorem lift {E A : Type} (p : E → Prop) (call : Result A) :
 Holds p (monadLift call : NJU_Log.Run E A) := List.Forall.nil

theorem liftM {E A : Type} (p : E → Prop) (call : Result A) :
 Holds p (liftM call : NJU_Log.Run E A) := List.Forall.nil

theorem record {E A : Type} (p : E → Prop) (event : Result A → E)
 (call : Result A) (clause : p (event call)) :
 Holds p (NJU_Log.record event call) := List.Forall.cons clause List.Forall.nil

theorem bind {E A B : Type} (p : E → Prop) (m : NJU_Log.Run E A)
 (k : A → NJU_Log.Run E B) (first : Holds p m)
 (next : ∀ a, Holds p (k a)) : Holds p (m >>= k) := by
 cases m with
 | mk result events =>
  cases result with
  | fail err => exact first
  | div => exact first
  | ok a => exact List.forall_append.mpr ⟨first,next a⟩

theorem branch {E A : Type} (p : E → Prop) (test : Prop) [Decidable test]
 (yes no : NJU_Log.Run E A) (hy : Holds p yes) (hn : Holds p no) :
 Holds p (if test then yes else no) := by split <;> assumption

theorem flow {E A B C : Type} (p : E → Prop)
 (test : core.ops.control_flow.ControlFlow B C)
 (yes : C → NJU_Log.Run E A) (no : B → NJU_Log.Run E A)
 (hy : ∀ c,Holds p (yes c)) (hn : ∀ b,Holds p (no b)) :
 Holds p (match test with | .Continue c=>yes c | .Break b=>no b) := by
 cases test <;> first | apply hy | apply hn

#print axioms pure
#print axioms lift
#print axioms liftM
#print axioms record
#print axioms bind
#print axioms branch
#print axioms flow
end NKK_LogClauses
