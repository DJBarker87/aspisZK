import NDO_JFt_ExactArray
import NDO_JFt_DigestInjective
set_option autoImplicit false
namespace AspisR1.JFt_DigestArray
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem shared (bytes : Slice U8) (arr : Array U8 32#usize) (same : bytes.val=arr.val) :
    core.array.TryFromSharedArraySlice.try_from 32#usize bytes=ok (.Ok arr) := by
  have size : Slice.len bytes=32#usize := by
    have h : bytes.length=32 := by change bytes.val.length=32;rw [same,arr.property];rfl
    scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos size]
  apply congrArg ok
  apply congrArg core.result.Result.Ok
  exact Subtype.ext same

theorem source (bytes : Slice U8) (arr : Array U8 32#usize) (same : bytes.val=arr.val)
    (digest : Array U32 8#usize)
    (call : AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok digest)) :
    atomic_statement.decode_digest_canonical arr=ok (.Ok digest) := by
  unfold AspisS6NativeSnapshotReadDigest.read_digest at call
  rw [shared bytes arr same] at call
  simpa only [bind_tc_ok,atomic_statement.unwrap_fixed_slice] using call

#print axioms shared
#print axioms source
end AspisR1.JFt_DigestArray
