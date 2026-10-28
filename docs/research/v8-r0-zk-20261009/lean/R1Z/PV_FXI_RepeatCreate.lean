import Init
set_option autoImplicit false
namespace PV_FXI_RepeatCreate

/-- Explicit state at the filesystem boundary. Durability is deliberately not
inferred from successful creation or from any observation-equality contract. -/
structure FileWorld where
  path : List UInt8
  descriptor : Nat
  contents : List UInt8
  durable : Bool
  exists : Bool
  errors : List Nat
  deriving DecidableEq

inductive OpenOutcome where
  | opened (descriptor : Nat)
  | alreadyExists
  deriving DecidableEq

/-- The checked create_new success / EEXIST branch, with no crash theorem.
This is an owned boundary reference, not a claimed OS-kernel axiom. -/
def createNew (w : FileWorld) : OpenOutcome × FileWorld :=
  if w.exists then (.alreadyExists,w)
  else (.opened w.descriptor,{w with exists := true, contents := [], durable := false})

def emptyWorld : FileWorld := ⟨[110],3,[],false,false,[]⟩
def createdWorld : FileWorld := (createNew emptyWorld).2

theorem first_result : (createNew emptyWorld).1 = .opened 3 := rfl
theorem second_result : (createNew createdWorld).1 = .alreadyExists := rfl

theorem same_path : createdWorld.path = emptyWorld.path := rfl

theorem distinct_results :
    (createNew emptyWorld).1 ≠ (createNew createdWorld).1 := by
  intro h
  cases h

/-- No pure callback on fixed options and fixed path represents both reached
worlds. This permits arbitrary carriers; it does not prohibit a new,
explicitly threaded world interpreter, or dictionaries indexed by world. -/
theorem no_fixed_callback {Options Path : Type}
    (callback : Options → Path → OpenOutcome) (options : Options) (path : Path) :
    ¬ (callback options path = (createNew emptyWorld).1 ∧
       callback options path = (createNew createdWorld).1) := by
  intro h
  exact distinct_results (h.1.symm.trans h.2)

/-- The obstruction also applies before projection to the outer Result.
A fixed decoder of the original complete callback result cannot repair it. -/
theorem no_fixed_complete_result {Options Path Complete : Type}
    (callback : Options → Path → Complete) (decode : Complete → OpenOutcome)
    (options : Options) (path : Path) :
    ¬ (decode (callback options path) = (createNew emptyWorld).1 ∧
       decode (callback options path) = (createNew createdWorld).1) :=
  no_fixed_callback (fun o p => decode (callback o p)) options path

#print axioms first_result
#print axioms second_result
#print axioms same_path
#print axioms distinct_results
#print axioms no_fixed_callback
#print axioms no_fixed_complete_result
end PV_FXI_RepeatCreate
