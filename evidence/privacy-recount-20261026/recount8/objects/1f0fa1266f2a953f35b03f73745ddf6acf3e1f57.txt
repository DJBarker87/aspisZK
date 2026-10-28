import Aeneas

/-! Owned operational reference for the deployed usize Range::next and the
Iterator::fold default body. Structural source binding is a separate obligation.
The Result callback retains failure/divergence; this is not a native-code claim. -/
namespace R1Z.PV_RDCD3_RangeFold
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Cursor where
  start : Nat
  stop : Nat
  deriving DecidableEq

/-- TrustedStep branch: read old start, advance it, then yield old start. -/
def next (r : Cursor) : Option Nat × Cursor :=
  if r.start < r.stop then (some r.start, ⟨r.start+1,r.stop⟩) else (none,r)

/-- Iterator::fold body with a proved exact termination budget. Exhaustion is
checked even at zero fuel, so insufficient fuel cannot silently return success. -/
def run {S : Type} (f : S → Nat → Result S) : Nat → Cursor → S → Result S
  | 0,r,acc => if r.start < r.stop then fail .undef else ok acc
  | fuel+1,r,acc =>
    match next r with
    | (none,_) => ok acc
    | (some x,r') => do let acc' ← f acc x; run f fuel r' acc'

/-- Ordered recurrence, with the same complete Result carrier as the loop. -/
def ordered {S : Type} (f : S → Nat → Result S) : Nat → Nat → S → Result S
  | 0,_,acc => ok acc
  | fuel+1,start,acc => do let acc' ← f acc start; ordered f fuel (start+1) acc'

theorem next_active (r : Cursor) (active : r.start < r.stop) :
    next r = (some r.start,⟨r.start+1,r.stop⟩) := by
  simp only [next,active,if_true]

theorem next_empty (r : Cursor) (empty : r.stop ≤ r.start) :
    next r = (none,r) := by
  simp only [next,show ¬r.start<r.stop from by omega,if_false]

/-- The unchecked native usize increment has a valid in-range result. -/
theorem increment_bound (r : Cursor) (active : r.start < r.stop)
    (bounded : r.stop ≤ 2^64-1) : r.start+1 ≤ 2^64-1 := by omega

theorem complete {S : Type} (f : S → Nat → Result S) (fuel start stop : Nat)
    (acc : S) (bound : stop = start+fuel) :
    run f fuel ⟨start,stop⟩ acc = ordered f fuel start acc := by
  induction fuel generalizing start acc with
  | zero => simp only [Nat.add_zero] at bound; subst stop; simp [run,ordered]
  | succ fuel ih =>
    have active : start < stop := by omega
    rw [run,next_active _ active,ordered]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro acc' _
    exact ih (start+1) acc' (by omega)

theorem complete_empty {S : Type} (f : S → Nat → Result S) (r : Cursor)
    (acc : S) (empty : r.stop ≤ r.start) : run f 0 r acc = ok acc := by
  simp only [run,show ¬r.start<r.stop from by omega,if_false]

theorem zero_to {S : Type} (f : S → Nat → Result S) (stop : Nat) (acc : S) :
    run f stop ⟨0,stop⟩ acc = ordered f stop 0 acc :=
  complete f stop 0 stop acc (by omega)

/-- The failure of the first callback is retained, including the error value. -/
theorem first_failure {S : Type} (f : S → Nat → Result S)
    (fuel start stop : Nat) (acc : S) (e : Error)
    (active : start < stop) (failed : f acc start = fail e) :
    run f (fuel+1) ⟨start,stop⟩ acc = fail e := by
  rw [run,next_active _ active]
  change (f acc start >>= fun acc' => run f fuel ⟨start+1,stop⟩ acc') = fail e
  rw [failed,bind_tc_fail]

#print axioms next_active
#print axioms next_empty
#print axioms increment_bound
#print axioms complete
#print axioms complete_empty
#print axioms zero_to
#print axioms first_failure
end R1Z.PV_RDCD3_RangeFold
