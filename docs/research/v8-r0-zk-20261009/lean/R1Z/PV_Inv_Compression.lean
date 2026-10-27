import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace R1Z.PV_Inv_Compression
variable {K : Type} [CommRing K]

/-- Exact mathematical loop of compress_tagged_tuple after M31 embedding. -/
def loop (lambda : K) : K → K → List K → K
 | acc,_,[] => acc
 | acc,power,x::xs => loop lambda (acc+power*x) (power*lambda) xs

def weighted (lambda : K) : K → List K → K
 | _,[] => 0
 | power,x::xs => power*x+weighted lambda (power*lambda) xs

theorem loop_eq (lambda acc power : K) (xs : List K) :
    loop lambda acc power xs=acc+weighted lambda power xs := by
  induction xs generalizing acc power with
  | nil => simp [loop,weighted]
  | cons x xs ih => rw [loop,weighted,ih]; ring

theorem affine_start (lambda tag : K) (xs : List K) :
    loop lambda tag lambda xs=tag+weighted lambda lambda xs := loop_eq _ _ _ _

#print axioms loop_eq
#print axioms affine_start
end R1Z.PV_Inv_Compression
