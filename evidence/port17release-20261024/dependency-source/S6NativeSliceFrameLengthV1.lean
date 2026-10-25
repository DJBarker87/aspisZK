import S6SliceFrameLengthV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6NativeSliceFrame
@[simp] theorem setSlice_length {T : Type} (output : Slice T) (start : Nat) (values : List T) :
    (output.setSlice! start values).length=output.length := by
  exact AspisS6SliceFrame.setSlice_length _ _ _
#print axioms setSlice_length
end AspisS6NativeSliceFrame
