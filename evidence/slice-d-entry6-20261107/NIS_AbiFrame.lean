import Aeneas
set_option autoImplicit false
namespace NIS_AbiFrame

structure Call where
  account : Nat
  first : Nat
  second : Nat
  deriving DecidableEq

def write {α : Type} (heap : Nat → α) (index : Nat) (value : α) : Nat → α :=
  fun k => if k=index then value else heap k

def chain {α : Type} (heap : Nat → α) (base : Nat) : List α → Nat → α
  | [] => heap
  | value::rest => chain (write heap base value) (base+1) rest

theorem same {α : Type} (heap : Nat → α) (index : Nat) (value : α) :
    write heap index value index=value := by simp [write]

theorem other {α : Type} (heap : Nat → α) (index k : Nat) (value : α)
    (different : k≠index) : write heap index value k=heap k := by simp [write,different]

/-- Arbitrary-offset native log windows compose over an unchanged complement. -/
theorem outside {α : Type} (heap : Nat → α) (base k : Nat) (values : List α)
    (away : k<base ∨ base+values.length≤k) : chain heap base values k=heap k := by
  induction values generalizing heap base with
  | nil => rfl
  | cons value rest ih =>
    rw [chain,ih (write heap base value) (base+1) (by simp only [List.length_cons] at away; omega)]
    exact other heap base k value (by simp only [List.length_cons] at away; omega)

theorem inside {α : Type} (heap : Nat → α) (base : Nat) (values : List α)
    (j : Nat) (within : j<values.length) : chain heap base values (base+j)=values[j] := by
  induction values generalizing heap base j with
  | nil => simp at within
  | cons value rest ih =>
    cases j with
    | zero =>
      change chain (write heap base value) (base+1) rest base=value
      rw [outside (write heap base value) (base+1) base rest (Or.inl (by omega))]
      exact same heap base value
    | succ j =>
      have bound : j<rest.length := by simp only [List.length_cons] at within; omega
      simpa only [chain,Nat.add_assoc,Nat.add_comm 1 j,List.getElem_cons_succ] using
        ih (write heap base value) (base+1) j bound

#print axioms same
#print axioms other
#print axioms outside
#print axioms inside
end NIS_AbiFrame
