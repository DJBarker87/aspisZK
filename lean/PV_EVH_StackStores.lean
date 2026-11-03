import PV_EVH_StackZero
set_option autoImplicit false
namespace PV_EVH_StackStores
open PV_EVH_StackZero (State)

/-- Captured register bytes and their physical store footprint. This records
memory only; native reads/writes/register observations are not declared silent. -/
structure Store where
  address : Nat
  size : Nat
  value : Nat → Nat

def Covers (s : Store) (p : Nat) : Prop := s.address ≤ p ∧ p < s.address+s.size
def Outside (s : Store) (p : Nat) : Prop := p < s.address ∨ s.address+s.size ≤ p

def put (s : Store) (w : State) : State :=
  {w with memory := fun p => if Covers s p then s.value (p-s.address) else w.memory p}

def run : List Store → State → State
  | [], w => w
  | s::rest,w => run rest (put s w)

theorem inside (s : Store) (w : State) (i : Nat) (h : i < s.size) :
    (put s w).memory (s.address+i) = s.value i := by
  simp only [put]
  rw [if_pos (by unfold Covers; omega),Nat.add_sub_cancel_left]

theorem outside (s : Store) (w : State) (p : Nat) (h : Outside s p) :
    (put s w).memory p = w.memory p := by
  simp only [put]
  rw [if_neg (by unfold Covers Outside at *; omega)]

theorem run_append (a b : List Store) (w : State) :
    run (a++b) w = run b (run a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons s rest ih => exact ih (put s w)

theorem outside_all (ss : List Store) (w : State) (p : Nat)
    (h : ∀ s ∈ ss, Outside s p) : (run ss w).memory p = w.memory p := by
  induction ss generalizing w with
  | nil => rfl
  | cons s rest ih =>
    exact (ih (put s w) (fun t ht => h t (List.mem_cons_of_mem s ht))).trans
      (outside s w p (h s List.mem_cons_self))

/-- A selected store supplies the byte; all later stores are disjoint.
Earlier stores may be arbitrary. No commutation of observation events occurs. -/
theorem selected (before after : List Store) (s : Store) (w : State)
    (i : Nat) (hi : i < s.size)
    (h : ∀ t ∈ after, Outside t (s.address+i)) :
    (run (before++s::after) w).memory (s.address+i) = s.value i := by
  rw [run_append]
  exact (outside_all after (put s (run before w)) _ h).trans
    (inside s (run before w) i hi)

/-- Only physical memory is updated here. Ownership transfer and native
observation installation must be connected separately, never inferred. -/
theorem frame (ss : List Store) (w : State) :
    (run ss w).frame = w.frame ∧ (run ss w).history = w.history ∧
    (run ss w).writes = w.writes ∧ (run ss w).barriers = w.barriers ∧
    (run ss w).drops = w.drops := by
  induction ss generalizing w with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons s rest ih => exact ih (put s w)

#print axioms inside
#print axioms outside
#print axioms run_append
#print axioms outside_all
#print axioms selected
#print axioms frame
end PV_EVH_StackStores
