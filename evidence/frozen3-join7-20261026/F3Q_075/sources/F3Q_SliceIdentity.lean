import MultiproofConeByteEquality
set_option autoImplicit false
namespace AspisR1.F3Q_SliceIdentity
open Aeneas Aeneas.Std

theorem slice (left right : Slice U8)
    (same : MultiproofConeCanonical.bytesOf left.val=MultiproofConeCanonical.bytesOf right.val) : left=right := by
  exact Subtype.ext (MultiproofConeByteEquality.bytes_injective same)

#print axioms slice
end AspisR1.F3Q_SliceIdentity
