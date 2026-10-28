import NDO_JFu_DigestCanonical
import NDO_JFu_DigestSlice
set_option autoImplicit false
namespace AspisR1.JFu_DigestSliceCanonical
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem source (bytes : Slice U8) (out : Array U32 8#usize)
    (accepted : AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out)) :
    JFu_DigestCanonical.Canonical out := by
  unfold AspisS6NativeSnapshotReadDigest.read_digest at accepted
  cases cast : core.array.TryFromSharedArraySlice.try_from 32#usize bytes with
  | fail e => simp only [cast,bind_tc_fail] at accepted;cases accepted
  | div => simp only [cast,bind_tc_div] at accepted;cases accepted
  | ok r =>
    cases r with
    | Err e => simp only [cast,bind_tc_ok,atomic_statement.unwrap_fixed_slice,bind_tc_fail] at accepted;cases accepted
    | Ok arr =>
      simp only [cast,bind_tc_ok,atomic_statement.unwrap_fixed_slice] at accepted
      exact JFu_DigestCanonical.source arr out accepted

#print axioms source
end AspisR1.JFu_DigestSliceCanonical
