import Aeneas

namespace R1Z.PV_RDCD4_SliceRange194
set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-- Owned backing-storage view of a native half-open slice. The caller checks
both ordering and upper bound before the raw view is formed. -/
def window {T : Type} (xs : List T) (start stop : Nat) : List T :=
  (xs.drop start).take (stop-start)

def index {T : Type} (xs : List T) (start stop : Nat) : Result (List T) :=
  if start ≤ stop ∧ stop ≤ xs.length then ok (window xs start stop)
  else fail .arrayOutOfBounds

theorem success {T : Type} (xs : List T) (start stop : Nat)
    (ordered : start ≤ stop) (bounded : stop ≤ xs.length) :
    index xs start stop = ok (window xs start stop) := by
  simp only [index,ordered,bounded,and_self,if_true]

theorem reversed {T : Type} (xs : List T) (start stop : Nat)
    (invalid : stop < start) : index xs start stop = fail .arrayOutOfBounds := by
  simp only [index,show ¬start ≤ stop from by omega,false_and,if_false]

theorem oversized {T : Type} (xs : List T) (start stop : Nat)
    (invalid : xs.length < stop) : index xs start stop = fail .arrayOutOfBounds := by
  simp only [index,show ¬stop ≤ xs.length from by omega,and_false,if_false]

theorem length {T : Type} (xs : List T) (start stop : Nat)
    (bounded : stop ≤ xs.length) : (window xs start stop).length = stop-start := by
  simp only [window,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

/-- Empty views retain no element, for every position, including a position
beyond the source (whose checked index still fails separately). -/
theorem empty {T : Type} (xs : List T) (n : Nat) : window xs n n = [] := by
  simp only [window,Nat.sub_self,List.take_zero]

/-- The identity view preserves every element and order; no allocation or
copy-property is assumed by this statement. -/
theorem full {T : Type} (xs : List T) : window xs 0 xs.length = xs := by
  simp only [window,Nat.sub_zero,List.drop_zero,List.take_length]

#print axioms success
#print axioms reversed
#print axioms oversized
#print axioms length
#print axioms empty
#print axioms full
end R1Z.PV_RDCD4_SliceRange194
