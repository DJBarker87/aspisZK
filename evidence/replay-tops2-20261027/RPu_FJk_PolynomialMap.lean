import RPu_FJk_ArrayList
import RPu_FIv_HornerAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PolynomialMap
variable {K L : Type} [Semiring K] [Semiring L]
def polynomial (theta : K) (xs : List K) : K := xs.foldr (fun x acc=>x+theta*acc) 0
theorem map (f : K →+* L) (theta : K) (xs : List K) :
    f (polynomial theta xs)=polynomial (f theta) (xs.map f) := by
  induction xs with
  | nil => exact f.map_zero
  | cons x xs ih =>
    change f (x+theta*polynomial theta xs)=f x+f theta*polynomial (f theta) (xs.map f)
    rw [map_add,map_mul,ih]
#print axioms map
end AspisR1.FJk_PolynomialMap
namespace AspisR1.FJk_NativePolynomial
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
theorem value (theta : K) (xs : List NQ) :
    FIv_HornerAlgebra.low theta xs=FJk_PolynomialMap.polynomial theta (xs.map decode) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change decode x+theta*FIv_HornerAlgebra.low theta xs=
      decode x+theta*FJk_PolynomialMap.polynomial theta (xs.map decode)
    rw [ih]
#print axioms value
end AspisR1.FJk_NativePolynomial
end
