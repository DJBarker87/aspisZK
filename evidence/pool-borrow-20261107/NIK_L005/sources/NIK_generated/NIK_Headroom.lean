import NIE_BorrowRelease
set_option autoImplicit false
namespace NIK_Headroom
open AspisR1.S2Trust

def Room (counter : Int) : Prop := 0 ≤ counter ∧ counter < maxCounter
def Reserve (counter : Int) (held : Nat) : Prop :=
  0 ≤ counter ∧ counter + (held : Int) < maxCounter

theorem held_room (counter : Int) (held : Nat) (h : Reserve counter held) :
    Room (counter + (held : Int)) := by
  constructor
  · have nonnegative : (0 : Int) ≤ (held : Int) := Int.natCast_nonneg held
    omega
  · exact h.2
#print axioms held_room

/-- One native loop step must maintain a bound including already retained
guards; an empty local guard list is not a valid arbitrary-prestate invariant. -/
theorem one_shared_step (counter : Int) (held : Nat)
    (reserve : Reserve counter (held + 1)) :
    Reserve counter held ∧ Room (counter + (held : Int) + 1) := by
  unfold Reserve Room at *
  simp only [Int.natCast_add, Int.natCast_one] at reserve
  constructor
  · constructor
    · exact reserve.1
    · omega
  · constructor
    · omega
    · exact reserve.2
#print axioms one_shared_step

theorem reserve_mono (counter : Int) (small large : Nat)
    (h : small ≤ large) (reserve : Reserve counter large) :
    Reserve counter small := by
  unfold Reserve at *
  constructor
  · exact reserve.1
  · omega
#print axioms reserve_mono

/-- No concrete production input or reachability assertion is made. -/
theorem extra_shared_can_saturate (counter : Int)
    (h : counter + 1 = maxCounter) : ¬ Room (counter + 1) := by
  intro room
  unfold Room at room
  omega
#print axioms extra_shared_can_saturate
end NIK_Headroom
