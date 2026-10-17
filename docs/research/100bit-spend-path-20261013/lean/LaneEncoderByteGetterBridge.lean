import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailByteGetterBridge
open Aeneas Aeneas.Std

def arrayGet (bytes : Array U8 32#usize) (i : Nat) (hi : i < 32) : U8 :=
  bytes.val[i]'
    (by
      have h := bytes.property
      have hi' : i < bytes.val.length := by
        rw [h]
        exact hi
      change i < bytes.val.length
      exact hi')

theorem arrayGet_eq_sliceGet (bytes : Array U8 32#usize) (i : Nat) (hi : i < 32) :
    arrayGet bytes i hi = (↑bytes)[i]'
      (by
        have h := bytes.property
        have hi' : i < bytes.val.length := by
          rw [h]
          exact hi
        simpa using hi') := by
  rfl

#print axioms arrayGet_eq_sliceGet
end AspisR1PairForestLaneEncoderTailByteGetterBridge
