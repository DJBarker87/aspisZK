import Aeneas
set_option autoImplicit false
namespace NEG_ProductAbstraction
/-- Integer specification for a wrapping multiplication site. This relation is
not a license to remove an actual Rust instruction without a native association. -/
def Product (width a b p : Nat) : Prop := p = (a * b) % 2^width

def machineProduct (width a b : Nat) : Nat := (a * b) % 2^width

theorem admissible (width a b : Nat) :
    Product width a b (machineProduct width a b) := by rfl

theorem unique (width a b p : Nat) (h : Product width a b p) :
    p = machineProduct width a b := h

theorem transfer (width a b : Nat) (P : Nat → Prop)
    (abstract : ∀ p, Product width a b p → P p) :
    P (machineProduct width a b) := abstract _ (admissible width a b)

/-- Products can be independent symbolic log entries provided each entry is
associated with the operands of the same reached native site. -/
theorem log_admissible (n width : Nat) (a b : Fin n → Nat) :
    ∀ i, Product width (a i) (b i) (machineProduct width (a i) (b i)) := by
  intro i
  exact admissible width (a i) (b i)

theorem log_transfer (n width : Nat) (a b : Fin n → Nat)
    (P : (Fin n → Nat) → Prop)
    (abstract : ∀ log, (∀ i, Product width (a i) (b i) (log i)) → P log) :
    P (fun i => machineProduct width (a i) (b i)) :=
  abstract _ (log_admissible n width a b)

/-- A relational arbitrary-prestate step transports invariants by induction.
The step refinement remains an explicit proof obligation. -/
theorem iterate_invariant {State : Type} (step : State → State)
    (I : State → Prop) (preserves : ∀ s, I s → I (step s))
    (initial : State) (h : I initial) (n : Nat) :
    I (Nat.rec initial (fun _ s => step s) n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact preserves _ ih

#print axioms admissible
#print axioms unique
#print axioms transfer
#print axioms log_admissible
#print axioms log_transfer
#print axioms iterate_invariant
end NEG_ProductAbstraction
