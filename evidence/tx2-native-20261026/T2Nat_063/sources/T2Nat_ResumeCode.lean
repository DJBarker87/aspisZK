import T2Nat_CodeEq
import T2Nat_ResumePrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ResumeCode
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Effect T2Nat_ResultEq T2Nat_CodeEq

def body (ops : ResumeOps) (bytes proof public1 : Slice U8)
    (v : transport.Variant) (consume : T2Nat_ResumePrefix.Tail) :
    Code (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
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
              let end1 ← liftResult (i7 - 32#usize)
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
                  liftResult (consume i4 end1 s6 a2)

theorem source (ops : ResumeOps) (bytes proof pub : Slice U8) (v : transport.Variant) :
    body ops bytes proof pub v (CheckpointBytes5Resume.tail ops bytes v) =
      CheckpointBytes5Resume.program ops bytes proof pub v := rfl

/-- Every successful Result/log return is transported, including a returned
error with its already consumed oracle prefix. No independent log is chosen. -/
theorem congr (ops : ResumeOps) (bytes proof pub : Slice U8) (v : transport.Variant)
    (left right : T2Nat_ResumePrefix.Tail)
    (same : ∀ next finish checksum digest,
      EqOk (left next finish checksum digest) (right next finish checksum digest)) :
    EqRun (body ops bytes proof pub v left) (body ops bytes proof pub v right) := by
  unfold body
  repeat
    first
    | exact T2Nat_CodeEq.lift (same _ _ _ _)
    | exact T2Nat_CodeEq.refl (pure _)
    | (apply T2Nat_CodeEq.bind (T2Nat_CodeEq.refl _); intro x; try rcases x with ⟨a,b⟩)
    | (simp only [Aeneas.Std.uncurry])
    | (split <;> try simp only [*])

#print axioms source
#print axioms congr
end AspisR1.T2Nat_ResumeCode
end
