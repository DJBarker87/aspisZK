import FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Prefix
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)

def sumPrefix {N : Usize} (parts k : Array NE N) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix parts k n + FIp_ArrayValue.value k n*FIp_ArrayValue.value parts n

theorem zero {N : Usize} (parts k : Array NE N) : sumPrefix parts k 0=0 := rfl

theorem succ {N : Usize} (parts k : Array NE N) (n : Nat) :
    sumPrefix parts k (n+1)=sumPrefix parts k n+FIp_ArrayValue.value k n*FIp_ArrayValue.value parts n := rfl

#print axioms zero
#print axioms succ
end AspisR1.FIp_Prefix
end
