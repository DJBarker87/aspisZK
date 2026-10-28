import NDO_FIv_EqualityLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityShape
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIv_NativeArray (value)

theorem step (left right : Array NQ 10#usize) (start n : Nat) :
    FIv_EqualityLoop.tail left right start (n+1)=
      (value left start*value right start+(1-value left start)*(1-value right start))*
        FIv_EqualityLoop.tail left right (start+1) n := by
  rw [FIv_EqualityLoop.tail]

#print axioms step
end AspisR1.FIv_EqualityShape
end
