import S2LeadInterface

/-! Interface countermodels only. Neither construction is asserted to be the
observation of a native run. Their purpose is to expose the missing observation
port: pure owned acceptance and child value theorems do not constrain Inputs. -/
set_option autoImplicit false
namespace AspisR1.S2Z.ScheduleLimits
open S2LeadInterface

def forgetClock {Observer : Type} (c : Inputs Observer) : Inputs Observer :=
  {c with clock := fun _ => 0}

def finishOnly {Observer : Type} (c : Inputs Observer) : Inputs Observer :=
  {c with reached := fun s => s = .finish}

/-- Changing only observation clocks does not change any owned function input.
A value-only acceptance theorem cannot rule out these invalid clocks. -/
theorem no_clock_from_values {Observer : Type} (c : Inputs Observer)
    (first : c.reached .tx1) (second : c.reached .tx2) :
    ¬ (∀ s t, s.rank < t.rank → (forgetClock c).reached s →
      (forgetClock c).reached t → (forgetClock c).clock s < (forgetClock c).clock t) := by
  intro order
  have bad := order .tx1 .tx2 (by decide) first second
  exact Nat.lt_irrefl 0 bad

/-- Reached sites also need actual source/child event provenance; no arbitrary
Inputs record is made prefix-closed by a successful pure child return. -/
theorem no_prefix_from_values {Observer : Type} (c : Inputs Observer) :
    ¬ (∀ s t, s.rank < t.rank → (finishOnly c).reached t →
      (finishOnly c).reached s) := by
  intro prefix
  have bad := prefix .tx1 .finish (by decide) rfl
  cases bad

#print axioms no_clock_from_values
#print axioms no_prefix_from_values
end AspisR1.S2Z.ScheduleLimits
