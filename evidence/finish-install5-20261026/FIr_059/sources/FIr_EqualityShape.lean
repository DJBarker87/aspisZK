import FIr_EqualityLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_EqualityShape
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic (NQ)
open FIr_NativeValue (K)
open FIr_NativeArray (value)

theorem step (left right : Array NQ 10#usize) (start n : Nat) :
    FIr_EqualityLoop.tail left right start (n+1)=
      (value left start*value right start+(1-value left start)*(1-value right start))*
        FIr_EqualityLoop.tail left right (start+1) n := by
  rw [FIr_EqualityLoop.tail]

#print axioms step
end AspisR1.FIr_EqualityShape
end
