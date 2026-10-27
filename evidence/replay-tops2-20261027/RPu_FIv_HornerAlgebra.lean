import RPu_FIv_Horner24
import RPu_FIv_Horner4
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_HornerAlgebra
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

def low (theta : K) : List NQ → K
  | [] => 0
  | x::xs => decode x+theta*low theta xs

theorem reversed (theta seed : K) (xs : List NQ) :
    FIv_Horner24.model theta xs.reverse seed=theta^xs.length*seed+low theta xs := by
  induction xs with
  | nil => simp only [FIv_Horner24.model,List.reverse_nil,List.foldl_nil,List.length_nil,pow_zero,one_mul,low,add_zero]
  | cons x xs ih =>
    simp only [FIv_Horner24.model,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,
      List.length_cons,low]
    change theta*FIv_Horner24.model theta xs.reverse seed+decode x=_
    rw [ih,pow_succ]
    ring

theorem four (theta seed : K) (xs : List NQ) :
    FIv_Horner4.model theta xs.reverse seed=theta^xs.length*seed+low theta xs :=
  reversed theta seed xs

#print axioms reversed
#print axioms four
end AspisR1.FIv_HornerAlgebra
end
