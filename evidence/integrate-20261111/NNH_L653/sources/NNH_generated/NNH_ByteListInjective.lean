import NND_CarrierInjective
set_option autoImplicit false
namespace NNH_ByteListInjective
open Aeneas Aeneas.Std NND_Carrier

theorem value (xs ys : List U8) (same : xs.map byte=ys.map byte) : xs=ys := by
 induction xs generalizing ys with
 | nil => cases ys with
   | nil => rfl
   | cons y ys => cases same
 | cons x xs ih => cases ys with
   | nil => cases same
   | cons y ys =>
    have equal := List.cons.inj same
    exact congrArg₂ List.cons (byte_injective equal.1) (ih ys equal.2)
#print axioms value
end NNH_ByteListInjective
