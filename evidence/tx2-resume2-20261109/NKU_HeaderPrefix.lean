import NKK_LogReduce
import NKU_HeaderValue
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderPrefix
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
def prefixValue {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) :
 NJU_Log.Run Event (core.result.Result (U8 × core.slice.iter.Iter U8) verifier.Error) := do

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
            pure (core.result.Result.Ok (i4,i6))

def tail (bytes : Slice U8) (next : U8) (it : core.slice.iter.Iter U8) :
 NJU_Log.Run Event (core.result.Result (U8 × Usize) verifier.Error) := do
 let (hit,_) ← NJU_Log.record (.headerAny it) (NJJ_Any.any it)
 if hit then pure (.Err .Checkpoint) else
 let «end» ← lift (Std.Usize.wrapping_sub (Slice.len bytes) 32#usize)
 pure (.Ok (next,«end»))
/-- Split the killed L145 shape before any: this theorem only factors the
unchanged header syntax and has no memory-intensive success interpretation. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8) :
 NKU_HeaderValue.value d bytes .S2=
 (do let reply ← prefixValue d bytes .S2
     NKK_Try.emitted reply (fun (next,it)=>tail bytes next it)) := by
 unfold NKU_HeaderValue.value prefixValue tail NKK_Try.emitted
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases])
#print axioms source
end NKU_HeaderPrefix
