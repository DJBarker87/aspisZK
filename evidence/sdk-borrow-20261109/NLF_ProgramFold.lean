import NLF_StateLaws
set_option autoImplicit false
namespace NLF_ProgramFold
open NLF_RefCell NLF_SdkModel NLF_ParentModel
inductive Command where
  | acquire (account : Nat) (kind : Kind)
  | deref (guard : Guard)
  | release (guard : Guard)
  | write (guard : Guard) (value : Payload)

def step (p : Parent) : Command → Parent
  | .acquire a k => (NLF_ParentModel.acquire p a k).1
  | .deref g => (NLF_ParentModel.deref p g).1
  | .release g => (NLF_ParentModel.release p g).1
  | .write g v => {p with state:=NLF_ViewLaws.write p.state g v}

def run (p : Parent) : List Command → Parent
  | [] => p
  | c::cs => run (step p c) cs

theorem step_invariant (p : Parent) (c : Command) (h : Invariant p) : Invariant (step p c) := by
  cases c with
  | acquire a k => exact acquire_preserves p a k h
  | deref g => exact deref_invariant p g h
  | release g => exact release_preserves p g h
  | write g v => exact NLF_StateLaws.write_invariant p g v h

theorem fold_invariant (p : Parent) (cs : List Command) (h : Invariant p) : Invariant (run p cs) := by
  induction cs generalizing p with
  | nil => exact h
  | cons c cs ih => exact ih (step p c) (step_invariant p c h)

theorem source_order (p : Parent) (xs ys : List Command) :
    run p (xs++ys)=run (run p xs) ys := by
  induction xs generalizing p with
  | nil => rfl
  | cons c cs ih => exact ih (step p c)

#print axioms step_invariant
#print axioms fold_invariant
#print axioms source_order
end NLF_ProgramFold
