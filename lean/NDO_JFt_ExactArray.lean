import NDO_JFt_ReadArray
set_option autoImplicit false
namespace AspisR1.JFt_ExactArray
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

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

theorem source (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    pool_v1.pair_terminal.exact N bytes=ok (.Ok arr) := by
  unfold pool_v1.pair_terminal.exact
  rw [cast N bytes arr same]
  rfl

#print axioms cast
#print axioms source
end AspisR1.JFt_ExactArray
