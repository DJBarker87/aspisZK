import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_CoinAddresses

/-- Generic cyclic counter; instantiate m=2^64. Key uniqueness is confined
to one complete cycle and never silently extended to an uncapped loop. -/
def counter (m c i : Nat) := (c+i)%m

theorem same_counter_iff (m c i j : Nat) :
    counter m c i=counter m c j ↔ Nat.ModEq m i j := by
  change Nat.ModEq m (c+i) (c+j) ↔ Nat.ModEq m i j
  constructor
  · exact Nat.ModEq.add_left_cancel' c
  · intro h
    change i%m=j%m at h
    change (c+i)%m=(c+j)%m
    rw [Nat.add_mod c i m,Nat.add_mod c j m,h]
#print axioms same_counter_iff

theorem first_cycle_unique (m c i j : Nat) (hi : i<m) (hj : j<m)
    (h : counter m c i=counter m c j) : i=j := by
  have hm:Nat.ModEq m i j:=(same_counter_iff m c i j).1 h
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hm
#print axioms first_cycle_unique

theorem repeats (m c i : Nat) : counter m c (i+m)=counter m c i := by
  simp [counter,Nat.add_mod,Nat.add_assoc]
#print axioms repeats

theorem native_cycle (c i : Nat) :
    counter (2^64) c (i+2^64)=counter (2^64) c i := repeats _ _ _
#print axioms native_cycle

structure Frame (Seed : Type) where
  seed : Seed
  attempt : Nat
  stream : Nat
  counter : Nat
  deriving DecidableEq

def frame {Seed : Type} (seed : Seed) (attempt stream modulus start i : Nat) : Frame Seed :=
  ⟨seed,attempt,stream,counter modulus start i⟩

theorem frame_unique {Seed : Type} (seed : Seed) (attempt stream m c i j : Nat)
    (hi : i<m) (hj : j<m)
    (h : frame seed attempt stream m c i=frame seed attempt stream m c j) : i=j := by
  exact first_cycle_unique m c i j hi hj (congrArg Frame.counter h)
#print axioms frame_unique

theorem stream_separated {Seed : Type} (seed seed' : Seed) (a a' s s' m c i j : Nat)
    (h : s≠s') : frame seed a s m c i≠frame seed' a' s' m c j := by
  intro he
  exact h (congrArg Frame.stream he)
#print axioms stream_separated
end PV_L2D_CoinAddresses
