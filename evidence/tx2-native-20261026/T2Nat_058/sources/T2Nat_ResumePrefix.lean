import T2Nat_ResultEq
import Port4A_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ResumePrefix
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq
abbrev Tail := U8 → Usize → Slice U8 → Array U8 32#usize →
  Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)

def body (ops : ResumeOps) {H : Type}
    (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H) (consume : Tail) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let i := Slice.len bytes
  let i1 ← ops.checkpointSize v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne (slicePartialEq ops
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← ops.tag v
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
              ops.headerAny i6
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← lift (Std.Usize.wrapping_sub i7 32#usize)
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize }
              let s3 ← lift (Array.to_slice (Array.make 1#usize [ proof ]))
              let a ← aspis_coredigestDigest32Inst.digest hash s3
              let b2 ←
                ops.ne core.cmp.PartialEqU8 s2 a
              if b2
              then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize }
                let s5 ←
                  lift (Array.to_slice (Array.make 1#usize [ public1 ]))
                let a1 ← aspis_coredigestDigest32Inst.digest hash s5
                let b3 ←
                  ops.ne core.cmp.PartialEqU8 s4
                    a1
                if b3
                then ok (core.result.Result.Err verifier.Error.Checkpoint)
                else
                  let s6 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                      bytes { start := end1 }
                  let s7 ←
                    lift (Array.to_slice
                      (Array.make 22#usize [
                        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
                        58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
                        99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8
                        ]))
                  let s8 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      bytes { «end» := end1 }
                  let s9 ←
                    lift (Array.to_slice (Array.make 2#usize [ s7, s8 ]))
                  let a2 ← aspis_coredigestDigest32Inst.digest hash s9
                  consume i4 end1 s6 a2

theorem source (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : H) :
    body ops D bytes proof pub v hash (Port4A_NativeReader.tail ops bytes v) =
      Port4A_NativeReader.resume ops D bytes proof pub v hash := rfl

/-- Generic continuation transport preserves the complete physical returned
pair and every returned error. All digest calls stay in this unchanged body. -/
theorem congr (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof pub : Slice U8) (v : transport.Variant) (hash : H)
    (left right : Tail) (same : ∀ next finish checksum digest,
      EqOk (left next finish checksum digest) (right next finish checksum digest)) :
    EqOk (body ops D bytes proof pub v hash left) (body ops D bytes proof pub v hash right) := by
  unfold body
  repeat
    first
    | exact same _ _ _ _
    | exact T2Nat_ResultEq.refl (ok _)
    | (apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _); intro x; try rcases x with ⟨a,b⟩)
    | (split <;> try simp only [*])

#print axioms source
#print axioms congr
end AspisR1.T2Nat_ResumePrefix
end
