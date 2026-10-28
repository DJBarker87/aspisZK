import R1Z.PV_RDB2D_CollectorTrace
namespace R1Z.PV_RDB2D_SparseShape
open Aeneas Aeneas.Std Result
set_option autoImplicit false

/-- The supplied Boolean predicate is the concrete zero/one test. The source
association to raw QM31 equality is separate; no canonicality is assumed here. -/
def trailing {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  (point.reverse.takeWhile isBoolean).length

def prefix {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  point.length-trailing isBoolean point

def capacity {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  2^prefix isBoolean point

theorem trailing_bound {K : Type} (isBoolean : K → Bool) (point : List K) :
    trailing isBoolean point≤point.length := by
  unfold trailing
  exact (List.length_takeWhile_le _ _).trans_eq (List.length_reverse _)

theorem split_length {K : Type} (isBoolean : K → Bool) (point : List K) :
    prefix isBoolean point+trailing isBoolean point=point.length := by
  have h := trailing_bound isBoolean point
  unfold prefix
  omega

theorem capacity_positive {K : Type} (isBoolean : K → Bool) (point : List K) :
    0<capacity isBoolean point := Nat.two_pow_pos _

theorem capacity_bound {K : Type} (isBoolean : K → Bool) (point : List K)
    (length : point.length=10) : capacity isBoolean point≤1024 := by
  have hp : prefix isBoolean point≤10 := by unfold prefix;omega
  exact Nat.pow_le_pow_right (by omega) hp

theorem same_public_point {K H : Type} (isBoolean : K → Bool) (point : List K) (left right : H) :
    (fun (_ : H) => capacity isBoolean point) left=(fun (_ : H) => capacity isBoolean point) right := rfl

#print axioms trailing_bound
#print axioms split_length
#print axioms capacity_positive
#print axioms capacity_bound
#print axioms same_public_point
end R1Z.PV_RDB2D_SparseShape
