import NMW_Fold
set_option autoImplicit false
noncomputable section
namespace NMW_Commands
open Aeneas Aeneas.Std Result AspisR1 NMW_FullDispatch NMW_Outcome
/-- Reify the emitted opaque call itself, retaining all original arguments. -/
inductive Command (A : Type) where
 | first (args : Args A)
 | second (args : Args A)
 | init (args : Args A)
 | write (args : Args A)
 | finalize (args : Args A)
 | reject

def ops {A : Type} : NMW_Symbolic.Ops A (Command A) where
 first := fun p a d => ok (.first ⟨p,a,d⟩)
 second := fun p a d => ok (.second ⟨p,a,d⟩)
 init := fun p a d => ok (.init ⟨p,a,d⟩)
 write := fun p a d => ok (.write ⟨p,a,d⟩)
 finalize := fun p a d => ok (.finalize ⟨p,a,d⟩)
def run {A W E : Type} (children : Children A W E) (before : W) :
 Result (Command A) → Outcome W E
 | .fail e => .stopped (.failure e) []
 | .div => .stopped .divergence []
 | .ok (.first args) => children.first args before
 | .ok (.second args) => children.second args before
 | .ok (.init args) => children.init args before
 | .ok (.write args) => children.write args before
 | .ok (.finalize args) => children.finalize args before
 | .ok .reject => .returned (.Err .InvalidInstructionData) before []

theorem first_plan {A : Type} (args : Args A)
 (domain : Hiq_ReleaseRoute.stage1 args.data) :
 NMW_Symbolic.process ops args.program args.accounts args.data = ok (.first args) := by
 rw [NMW_Branches.first _ _ _ _ domain]
 rfl
theorem second_plan {A : Type} (args : Args A)
 (domain : Hiq_ReleaseRoute.asq8 args.data) :
 NMW_Symbolic.process ops args.program args.accounts args.data = ok (.second args) := by
 rw [NMW_Branches.second _ _ _ _ domain]
 rfl

theorem entry_plan {A : Type} (args : Args A) :
 NMW_Symbolic.entry ops .reject args.program args.accounts args.data =
 ok (match Hiq_ReleaseRoute.route args.data with
 | .first => .first args
 | .second => .second args
 | .reject => .reject) := by
 rw [NMW_Branches.entry_total]
 cases Hiq_ReleaseRoute.route args.data <;> rfl
/-- Exact full-outcome interpretation of the source-reified child command.
This is a forward source interpretation, not an inverse endpoint association. -/
theorem entry_forward {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) :
 run children before (NMW_Symbolic.entry ops .reject args.program args.accounts args.data) =
 entry children args before := by
 rw [entry_plan,NMW_FullDispatch.entry_total]
 cases Hiq_ReleaseRoute.route args.data <;> rfl

theorem process_forward {A W E : Type} (children : Children A W E)
 (args : Args A) (before : W) (domain : NMW_RowSpecs.Release args.data) :
 run children before (NMW_Symbolic.process ops args.program args.accounts args.data) =
 process children args before := by
 rcases domain with one | two
 · rw [first_plan args one,process_first children args before one]
   rfl
 · rw [second_plan args two,process_second children args before two]
   rfl
#print axioms first_plan
#print axioms second_plan
#print axioms entry_plan
#print axioms entry_forward
#print axioms process_forward
end NMW_Commands
end
