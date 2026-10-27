import Port4A_NativeReader
import Port4A_ReaderNormalize
set_option autoImplicit false
namespace AspisR1.Port8EFF_NativeReader
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
-- Current emitted parent: wrapping subtraction and current native decoder tail.
def program (ops : ResumeOps) (bytes proof public1 : Slice U8)
    (v : transport.Variant) : Code (core.result.Result
      (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let i := Slice.len bytes
  let i1 ← liftResult (ops.checkpointSize v)
  if i != i1
  then pure (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ← liftResult (
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize })
    let b ← liftResult (
      core.cmp.impls.PartialEqShared.ne (slicePartialEq ops
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ]))
    if b
    then pure (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← liftResult (Slice.index_usize bytes 8#usize)
      let i3 ← liftResult (ops.tag v)
      if i2 != i3
      then pure (core.result.Result.Err verifier.Error.Checkpoint)
      else
        let i4 ← liftResult (Slice.index_usize bytes 9#usize)
        if i4 > 22#u8
        then pure (core.result.Result.Err verifier.Error.Checkpoint)
        else
          let i5 ← liftResult (Slice.index_usize bytes 10#usize)
          if i5 != 1#u8
          then pure (core.result.Result.Err verifier.Error.Checkpoint)
          else
            let s1 ← liftResult (
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := 11#usize, «end» := 16#usize })
            let i6 ← liftResult (core.slice.Slice.iter s1)
            let (b1, _) ← liftResult (ops.headerAny i6)
            if b1
            then pure (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← liftResult (lift (Std.Usize.wrapping_sub i7 32#usize))
              let s2 ← liftResult (
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize })
              let s3 ← liftResult (lift (Array.to_slice (Array.make 1#usize [ proof ])))
              let a ← read s3
              let b2 ← liftResult (
                ops.ne core.cmp.PartialEqU8 s2 a)
              if b2
              then pure (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ← liftResult (
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize })
                let s5 ← liftResult (
                  lift (Array.to_slice (Array.make 1#usize [ public1 ])))
                let a1 ← read s5
                let b3 ← liftResult (
                  ops.ne core.cmp.PartialEqU8 s4
                    a1)
                if b3
                then pure (core.result.Result.Err verifier.Error.Checkpoint)
                else
                  let s6 ← liftResult (
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                      bytes { start := end1 })
                  let s7 ← liftResult (
                    lift (Array.to_slice
                      (Array.make 22#usize [
                        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
                        58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
                        99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8
                        ])))
                  let s8 ← liftResult (
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      bytes { «end» := end1 })
                  let s9 ← liftResult (
                    lift (Array.to_slice (Array.make 2#usize [ s7, s8 ])))
                  let a2 ← read s9
                  liftResult (Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2)

private theorem if_tail {A : Type} (p : Prop) [Decidable p] (a b c : A)
    (h : b=c) : (if p then a else b)=(if p then a else c) := by rw [h]

theorem source (ops : ResumeOps) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : Hash) :
    erase D hash (program ops bytes proof pub v)=
      Port4A_NativeReader.resume ops D bytes proof pub v hash := by
  simp only [program,erase_bind,erase_lift,erase_read,erase_pure,erase_ite]
  unfold Port4A_NativeReader.resume
  repeat
    first
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value success
    | apply if_tail
  rfl

#print axioms if_tail
#print axioms source
end AspisR1.Port8EFF_NativeReader
