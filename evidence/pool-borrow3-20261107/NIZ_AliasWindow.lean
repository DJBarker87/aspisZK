import NIZ_KeyEquality
set_option autoImplicit false
namespace NIZ_AliasWindow

def right {C : Type} [DecidableEq C] (a b : C) : Nat := if b = a then 0 else 1

def observer {C : Type} [DecidableEq C] (a b o : C) : Nat :=
  if o = a then 0 else if o = b then right a b else 2

def bytes {C : Type} {V : Type} (memory : C → V) (a b o : C) (i : Nat) : V :=
  if i = 0 then memory a else if i = 1 then memory b else memory o

theorem right_bound {C : Type} [DecidableEq C] (a b : C) : right a b < 3 := by
  by_cases h : b = a <;> simp [right,h]
#print axioms right_bound

theorem observer_bound {C : Type} [DecidableEq C] (a b o : C) : observer a b o < 3 := by
  by_cases ha : o = a <;> by_cases hb : o = b <;> by_cases h : b = a <;>
    simp [observer,right,ha,hb,h]
#print axioms observer_bound

theorem right_value {C : Type} {V : Type} [DecidableEq C]
    (memory : C → V) (a b o : C) : bytes memory a b o (right a b) = memory b := by
  by_cases h : b = a <;> simp [right,bytes,h]
#print axioms right_value

theorem observer_value {C : Type} {V : Type} [DecidableEq C]
    (memory : C → V) (a b o : C) : bytes memory a b o (observer a b o) = memory o := by
  by_cases ha : o = a <;> by_cases hb : o = b <;> by_cases h : b = a <;>
    simp_all [observer,right,bytes]
#print axioms observer_value

/-- All alias partitions of two read cells and one observed frame cell fit the
native three-byte carrier. No arbitrary-memory size bound is imposed. -/
theorem observer_alias {C : Type} [DecidableEq C] (a b o : C) :
    observer a b o = right a b ↔ o = b := by
  by_cases ha : o = a <;> by_cases hb : o = b <;> by_cases h : b = a <;>
    simp_all [observer,right]
#print axioms observer_alias

/-- Transport exactly K006's zero/frame assertions; no sign or magnitude law.
Native address/readability/loop association is separately pinned in the register. -/
theorem transport_cut {C : Type} [DecidableEq C] (memory : C → Nat)
    (a b o : C) (reply : Int) (afterObserver : Nat)
    (zero : reply = 0 ↔ bytes memory a b o 0 = bytes memory a b o (right a b))
    (frame : afterObserver = bytes memory a b o (observer a b o)) :
    (reply = 0 ↔ memory a = memory b) ∧ afterObserver = memory o := by
  constructor
  · have left : bytes memory a b o 0 = memory a := by simp [bytes]
    rw [left, right_value] at zero
    exact zero
  · simpa only [observer_value] using frame
#print axioms transport_cut
end NIZ_AliasWindow
