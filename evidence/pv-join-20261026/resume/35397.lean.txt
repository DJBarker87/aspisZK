import R1Z.PDict_IOCarriers
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Options
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Options := PDict_PathTypes.std.fs.OpenOptions

-- P6 associations: complete_options_state_and_new, write_loan_and_frame,
-- create_new_loan_and_frame, mode_loan_and_frame. These cover every primitive
-- field state of the pinned Unix schema and the returned receiver identity.
-- The failed baseline borrowed-setter emission is retained, not used.
def make : Result Options := .ok
  ⟨false,false,false,false,false,false,0#i32,438#u32⟩

def write (o : Options) (flag : Bool) : Result (Options × (Options → Options)) :=
  .ok ({o with write := flag},id)

def createNew (o : Options) (flag : Bool) : Result (Options × (Options → Options)) :=
  .ok ({o with create_new := flag},id)

def mode (o : Options) (value : U32) : Result (Options × (Options → Options)) :=
  .ok ({o with mode := value},id)

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_IOCarriers.native base)) :
    @ExternalFuns (PDict_IOCarriers.native base) :=
  letI : ExternalTypes := PDict_IOCarriers.native base
  { PDict_IOCarriers.selected base ops with
    op19 := make,op20 := write,op21 := createNew,op24 := mode }

theorem op19_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_IOCarriers.native base)) :
    (selected base ops).op19 = .ok
      ⟨false,false,false,false,false,false,0#i32,438#u32⟩ := rfl

theorem op20_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_IOCarriers.native base)) (o : Options) (b : Bool) :
    (selected base ops).op20 o b = .ok ({o with write := b},id) := rfl

theorem op21_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_IOCarriers.native base)) (o : Options) (b : Bool) :
    (selected base ops).op21 o b = .ok ({o with create_new := b},id) := rfl

theorem op24_installed (base : ExternalTypes)
    (ops : @ExternalFuns (PDict_IOCarriers.native base)) (o : Options) (m : U32) :
    (selected base ops).op24 o m = .ok ({o with mode := m},id) := rfl

/-- Backward continuation returns the entire future receiver state, including
any further caller updates made through the returned mutable borrow. -/
theorem write_back (o after : Options) (b : Bool) :
    write o b = .ok ({o with write := b},fun x => x) ∧ id after = after := ⟨rfl,rfl⟩

#print axioms op19_installed
#print axioms op20_installed
#print axioms op21_installed
#print axioms op24_installed
#print axioms write_back
end R1Z.PDict_Options
