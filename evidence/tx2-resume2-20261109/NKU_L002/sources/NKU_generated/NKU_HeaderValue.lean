import NKU_State
import NKK_HeaderSource
import NJJ_Any
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderValue
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
/-- Native header G of NKK_K028 (controls K029/K030). Earlier guards are
short-circuiting; the actual bytes[11..16] iterator is passed to NJJ_Any.
Only the pinned library model replaces the external any slot. -/
def value {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) :
 NJU_Log.Run Event (core.result.Result (U8 × Usize) verifier.Error) := do

  let i := Slice.len bytes
  let i1 ← (fun v=>CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant v)) v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne ((Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← (fun v=>CheckpointBytes4Ops.tag (NIL_Carriers.variant v)) v
      if i2 != i3
      then ok (core.result.Result.Err verifier.Error.Checkpoint)
      else
        let i4 ← Slice.index_usize bytes 9#usize
        if i4 > 22#u8
        then ok (core.result.Result.Err verifier.Error.Checkpoint)
        else
          let i5 ← Slice.index_usize bytes 10#usize
          if i5 != 1#u8
          then ok (core.result.Result.Err verifier.Error.Checkpoint)
          else
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := 11#usize, «end» := 16#usize }
            let i6 ← core.slice.Slice.iter s1
            let (b1, _) ←
              NJU_Log.record (.headerAny i6) (NJJ_Any.any i6)
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← lift (Std.Usize.wrapping_sub i7 32#usize)
              pure (core.result.Result.Ok (i4,end1))

theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) :
 NKK_HeaderSource.header d bytes v=value d bytes v := by
 unfold NKK_HeaderSource.header value NJU_ResumeObserved.recordAny
 simp only [NJJ_Any.installed]
#print source
#print axioms source
end NKU_HeaderValue
