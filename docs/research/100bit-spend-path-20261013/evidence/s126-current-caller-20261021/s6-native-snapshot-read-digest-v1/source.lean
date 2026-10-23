import S6NativeSnapshotEncodeTotalV1
import S6SourcePaymentCommonDecodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotReadDigest
open AspisR1TerminalDecoder

@[step] theorem unwrap_spec {T : Type} (copy : core.marker.Copy T) (value : T) :
    atomic_statement.unwrap_fixed_slice copy (core.result.Result.Ok value)
      ⦃ result => result=value ⦄ := by
  exact WP.spec_ok.mpr rfl

@[step] theorem digest_spec (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        AspisS6SourceCodec.DigestContents.chunks digest=bytes.val ⦄ := by
  exact AspisS6NativeDigestAcceptedInverse.decoded_contents bytes

/-- Exact original cast/unwrap/decode sequence. All callees are actual native
or standard implementations; the parent's reached slice length discharges panic. -/
def read_digest (bytes : Slice U8) :
    Result (core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError) := do
  let converted ← core.array.TryFromSharedArraySlice.try_from 32#usize bytes
  let array ← atomic_statement.unwrap_fixed_slice
    (Shared0T.Insts.CoreMarkerCopy (Array U8 32#usize)) converted
  atomic_statement.decode_digest_canonical array

@[step] theorem read_digest_spec (bytes : Slice U8) (size : bytes.length=32) :
    read_digest bytes ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
      AspisS6SourceCodec.DigestContents.chunks digest=bytes.val ⦄ := by
  unfold read_digest
  step*
  all_goals (cases converted <;> simp_all)
  all_goals step*
  all_goals simp_all

#print axioms unwrap_spec
#print axioms digest_spec
#print axioms read_digest_spec
end AspisS6NativeSnapshotReadDigest
