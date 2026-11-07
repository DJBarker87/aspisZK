import NMX_ErasureLaws
set_option autoImplicit false
noncomputable section
namespace NMX_StepCore
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ProgramLaws
/-- A single entered call includes all returning and stopped arms. -/
theorem call {W E A : Type} (handler : Handler W E) (command : Command A) (before : W) :
 eval handler (NMX_SourceProgram.call command) before = handler command before := by
 unfold NMX_SourceProgram.call
 rw [eval]
 cases handler command before with
 | stopped es cause => rfl
 | returned reply post es =>
   cases reply with
   | Err e => rfl
   | Ok a => simp only [eval,prepend,List.append_nil]

theorem entered {W E A B : Type} (handler : Handler W E) (command : Command A)
 (next : A → Program B) (before : W) :
 eval handler (NMX_Program.bind (NMX_SourceProgram.call command) next) before =
 continueRun handler next (handler command before) := by
 rw [eval_bind,call]

/-- One raw std operation, with no event or returned-error coercion. -/
theorem raw (ops : Ops) (owners : Owners) {A : Type}
 (value : Result A) (next : A → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.raw value) next) ()) =
 match value with
 | .ok a => NMX_ValueLink.erase (eval (source ops owners) (next a) ())
 | .fail e => .fail e
 | .div => .div := by
 unfold NMX_SourceProgram.raw
 rw [entered]
 exact NMX_ErasureLaws.continue_raw _ _ [] value
#print axioms call
#print axioms entered
#print axioms raw
end NMX_StepCore
end
