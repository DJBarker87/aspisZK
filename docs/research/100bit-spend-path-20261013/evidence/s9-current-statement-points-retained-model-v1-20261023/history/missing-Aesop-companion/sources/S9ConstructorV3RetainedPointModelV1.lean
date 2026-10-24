import S9ConstructorV3VectorMeaningV1
import R0P.SemView
set_option autoImplicit false
namespace AspisR1S9ConstructorV3RetainedPointModelV1
open AspisR1S9ConstructorV3VectorMeaningV1

/-- Exact carrier/index transport to the existing retained semantic view.
No generated recurrence cell is reduced. -/
theorem succCarry_eq_retained (p : Nat → ExactQM) (k : Nat) :
    succCarry p k = R0P.SemSource.succCarry (fun i : Fin 10 => p i.val) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (if k<10 then p (9-k) else 0)*succCarry p k =
      (if k<10 then p (9-k) else 0)*R0P.SemSource.succCarry (fun i : Fin 10 => p i.val) k
    rw [ih]

theorem successorPoint_eq_retained (p : Nat → ExactQM) (i : Fin 10) :
    successorPoint p i.val = R0P.SemSource.successorPoint (fun j : Fin 10 => p j.val) i := by
  unfold successorPoint R0P.SemSource.successorPoint
  rw [succCarry_eq_retained]

#print axioms succCarry_eq_retained
#print axioms successorPoint_eq_retained
end AspisR1S9ConstructorV3RetainedPointModelV1
