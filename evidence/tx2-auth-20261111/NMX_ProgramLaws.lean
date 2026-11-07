import NMX_Program
set_option autoImplicit false
noncomputable section
namespace NMX_ProgramLaws
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_Program
theorem prepend_nil {W E A : Type} (outcome : End W E A) :
 prepend [] outcome = outcome := by cases outcome <;> rfl
/-- Prefix composition preserves order also on nonreturning child arms. -/
theorem prepend_assoc {W E A : Type} (xs ys : List E) (outcome : End W E A) :
 prepend xs (prepend ys outcome) = prepend (xs ++ ys) outcome := by
 cases outcome <;> simp only [prepend,List.append_assoc]

def continueRun {W E A B : Type} (handler : Handler W E)
 (next : A → Program B) : End W E A → End W E B
 | .returned (.Ok a) post es => prepend es (eval handler (next a) post)
 | .returned (.Err e) post es => .returned (.Err e) post es
 | .stopped es cause => .stopped es cause

theorem continue_prepend {W E A B : Type} (handler : Handler W E)
 (next : A → Program B) (es : List E) (outcome : End W E A) :
 continueRun handler next (prepend es outcome) =
 prepend es (continueRun handler next outcome) := by
 cases outcome with
 | stopped events cause => rfl
 | returned reply post events =>
   cases reply with
   | Err e => rfl
   | Ok a => exact (prepend_assoc es events _).symm

theorem eval_bind {W E A B : Type} (handler : Handler W E)
 (term : Program A) (next : A → Program B) (before : W) :
 eval handler (NMX_Program.bind term next) before =
 continueRun handler next (eval handler term before) := by
 induction term generalizing before with
 | ret a => simp only [NMX_Program.bind,eval,continueRun,prepend_nil]
 | reject e => rfl
 | stop s => rfl
 | @step C cmd rest ih =>
   simp only [NMX_Program.bind,eval]
   cases h : handler cmd before with
   | stopped es s => rfl
   | returned reply post es =>
     cases reply with
     | Err e => rfl
     | Ok c =>
       change prepend es (eval handler (NMX_Program.bind (rest c) next) post) =
         continueRun handler next (prepend es (eval handler (rest c) post))
       rw [ih c post,continue_prepend]
#print axioms prepend_nil
#print axioms prepend_assoc
#print axioms continue_prepend
#print axioms eval_bind
end NMX_ProgramLaws
end
