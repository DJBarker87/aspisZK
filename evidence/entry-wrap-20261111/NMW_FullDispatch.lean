import NMW_Branches
import NMW_Outcome
set_option autoImplicit false
noncomputable section
namespace NMW_FullDispatch
open Aeneas Aeneas.Std Result AspisR1 NMW_Outcome
structure Args (Account : Type) where
 program : Hiq_DispatchSource.Key
 accounts : Slice Account
 data : Slice U8
abbrev Child (A W E : Type) := Args A → W → Outcome W E
/-- Intermediate interpretation of opaque children. World is the ENTIRE child
world (accounts/cell identities/counters/tokens/return data/ambient state).
No resource or observation projection is permitted at instantiation. -/
structure Children (A W E : Type) where
 first : Child A W E
 second : Child A W E
 init : Child A W E
 write : Child A W E
 finalize : Child A W E
def ops {A W E : Type} (children : Children A W E) (before : W) :
 NMW_Symbolic.Ops A (Outcome W E) where
 first := fun p a d => ok (children.first ⟨p,a,d⟩ before)
 second := fun p a d => ok (children.second ⟨p,a,d⟩ before)
 init := fun p a d => ok (children.init ⟨p,a,d⟩ before)
 write := fun p a d => ok (children.write ⟨p,a,d⟩ before)
 finalize := fun p a d => ok (children.finalize ⟨p,a,d⟩ before)
def finish {W E : Type} : Result (Outcome W E) → Outcome W E
 | .ok value => value
 | .fail error => .stopped (.failure error) []
 | .div => .stopped .divergence []
/-- Direct universal interpretation of the fresh emitted control tree. The
selected opaque child supplies its full outcome, including stopped prefix;
there is no post-child caller operation in either frozen wrapper. -/
def process {A W E : Type} (children : Children A W E) (args : Args A)
 (before : W) : Outcome W E :=
 finish (NMW_Symbolic.process (ops children before) args.program args.accounts args.data)
def entry {A W E : Type} (children : Children A W E) (args : Args A)
 (before : W) : Outcome W E :=
 finish (NMW_Symbolic.entry (ops children before)
   (.returned (.Err .InvalidInstructionData) before [])
   args.program args.accounts args.data)

theorem process_first {A W E : Type} (children : Children A W E) (args : Args A)
 (before : W) (domain : Hiq_ReleaseRoute.stage1 args.data) :
 process children args before = children.first args before := by
 rw [process,NMW_Branches.first _ _ _ _ domain]
 rfl

theorem process_second {A W E : Type} (children : Children A W E) (args : Args A)
 (before : W) (domain : Hiq_ReleaseRoute.asq8 args.data) :
 process children args before = children.second args before := by
 rw [process,NMW_Branches.second _ _ _ _ domain]
 rfl

theorem entry_total {A W E : Type} (children : Children A W E) (args : Args A)
 (before : W) :
 entry children args before = match Hiq_ReleaseRoute.route args.data with
 | .first => children.first args before
 | .second => children.second args before
 | .reject => .returned (.Err .InvalidInstructionData) before [] := by
 rw [entry,NMW_Branches.entry_total]
 cases Hiq_ReleaseRoute.route args.data <;> rfl
#print axioms process_first
#print axioms process_second
#print axioms entry_total
end NMW_FullDispatch
end
