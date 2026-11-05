import Aeneas
set_option autoImplicit false
namespace NHY_ExactArray
open Aeneas Aeneas.Std Result WP

theorem cast (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes=ok (.Ok arr) := by
  have size : bytes.length=N.val := by change bytes.val.length=N.val;rw [same,arr.property]
  have spec : core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes
      ⦃ out => out=.Ok arr ⦄ := by
    step*
    cases out with
    | Err e => exact False.elim (out_post size)
    | Ok value =>
      congr 1
      exact Subtype.ext (out_post.1.trans same)
  obtain ⟨out,call,equal⟩:=WP.spec_imp_exists spec
  rw [equal] at call
  exact call

#print axioms cast
end NHY_ExactArray
