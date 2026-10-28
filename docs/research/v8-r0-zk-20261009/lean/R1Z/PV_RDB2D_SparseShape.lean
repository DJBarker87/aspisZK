import R1Z.PV_RDB2D_CollectorTrace
namespace R1Z.PV_RDB2D_SparseShape
open Aeneas Aeneas.Std Result
set_option autoImplicit false

/-- The supplied Boolean predicate is the concrete zero/one test. The source
association to raw QM31 equality is separate; no canonicality is assumed here. -/
def trailing {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  (point.reverse.takeWhile isBoolean).length

def prefixLen {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  point.length-trailing isBoolean point

def capacity {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  2^prefixLen isBoolean point

theorem trailing_bound {K : Type} (isBoolean : K → Bool) (point : List K) :
    trailing isBoolean point≤point.length := by
  unfold trailing
  have bound : ∀ xs : List K, (xs.takeWhile isBoolean).length≤xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases h : isBoolean x <;> simp [List.takeWhile,h] <;> omega
  exact (bound point.reverse).trans_eq (List.length_reverse _)

theorem split_length {K : Type} (isBoolean : K → Bool) (point : List K) :
    prefixLen isBoolean point+trailing isBoolean point=point.length := by
  have h := trailing_bound isBoolean point
  unfold prefixLen
  omega

theorem capacity_positive {K : Type} (isBoolean : K → Bool) (point : List K) :
    0<capacity isBoolean point := Nat.two_pow_pos _

theorem capacity_bound {K : Type} (isBoolean : K → Bool) (point : List K)
    (length : point.length=10) : capacity isBoolean point≤1024 := by
  have hp : prefixLen isBoolean point≤10 := by unfold prefixLen;omega
  exact Nat.pow_le_pow_right (by omega) hp

theorem same_public_point {K H : Type} (isBoolean : K → Bool) (point : List K) (left right : H) :
    (fun (_ : H) => capacity isBoolean point) left=(fun (_ : H) => capacity isBoolean point) right := rfl

#print axioms trailing_bound
#print axioms split_length
#print axioms capacity_positive
#print axioms capacity_bound
#print axioms same_public_point
end R1Z.PV_RDB2D_SparseShape
