import Port6CK_Tail
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Header
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port6CK_Semantic (Unwrap)
open Port6CK_Ops (ops)
def header (ops : ResumeOps) (bytes proof public1 : Slice U8)
    (v : transport.Variant)
    (next : U8 → Usize → Slice U8 → Digest → Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) : Code (core.result.Result
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
                  liftResult (next i4 end1 s6 a2)


theorem tail_same (leaves : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (last : Usize) (suffix : Slice U8) (digest : Digest) :
    CheckpointBytes5Resume.tail leaves bytes v next last suffix digest =
      Port4A_NativeReader.tail leaves bytes v next last suffix digest := by rfl

theorem current_source (reserved : Bool) (unwrap : Unwrap) (bytes proof pub : Slice U8) :
    CheckpointBytes5Resume.program (ops reserved unwrap) bytes proof pub .S2 =
    header (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2
      (Port4A_NativeReader.tail (ops reserved unwrap) bytes .S2) := by
  unfold CheckpointBytes5Resume.program header
  simp only [tail_same]
  try rfl

theorem reference_source (reserved : Bool) (bytes proof pub : Slice U8) :
    CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2 =
    header (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2
      (Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes .S2) := by
  unfold CheckpointBytes5Resume.program header
  simp only [tail_same]
  try rfl

theorem size_s2 : CheckpointBytes4Ops.checkpointSize .S2=ok 1768#usize := by
  unfold CheckpointBytes4Ops.checkpointSize CheckpointBytes4Ops.finalLen
  simp only [bind_tc_ok]
  rw [Port4A_ReaderInstall.mul_value _ _ (by decide),bind_tc_ok,
    Port4A_ReaderInstall.add_value _ _ (by decide)]
  rfl

/-- The SAME accepted current source program returns the SAME pair and full
ordered log under the retained reader. All digest operands stay literal. -/
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (bytes proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (before after : Log)
    (actual : run D hash (CheckpointBytes5Resume.program (ops reserved unwrap) bytes proof pub .S2) before = ok (.Ok (p,a),after)) :
    run D hash (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2) before = ok (.Ok (p,a),after) := by
  rw [current_source] at actual
  rw [reference_source]
  unfold header at actual ⊢
  dsimp only [CheckpointBytes4Ops.ops] at actual ⊢
  simp only [run_bind,run_lift,run_read,run_pure,run_ite,
    bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
  obtain ⟨size,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  rw [called]
  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
  have sizeEq : size=1768#usize := Result.ok.inj (called.symm.trans size_s2)
  by_cases reject : (Slice.len bytes != size)=true
  · try simp only [if_pos reject] at actual
    cases actual
  · try simp only [if_neg reject] at actual ⊢
    have length : bytes.val.length=1768 := by
      have same : Slice.len bytes=size := by simpa only [bne_iff_ne,ne_eq,not_not] using reject
      have values := congrArg UScalar.val (same.trans sizeEq)
      exact values
    obtain ⟨magic,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    obtain ⟨badMagic,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    rw [called]
    simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
    by_cases reject : (badMagic)=true
    · try simp only [if_pos reject] at actual
      cases actual
    · try simp only [if_neg reject] at actual ⊢
      obtain ⟨tagByte,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
      rw [called]
      simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
      obtain ⟨tag,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
      rw [called]
      simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
      by_cases reject : (tagByte != tag)=true
      · try simp only [if_pos reject] at actual
        cases actual
      · try simp only [if_neg reject] at actual ⊢
        obtain ⟨nextByte,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
        rw [called]
        simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
        by_cases reject : nextByte > 22#u8
        · try simp only [if_pos reject] at actual
          cases actual
        · try simp only [if_neg reject] at actual ⊢
          obtain ⟨version,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
          rw [called]
          simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
          by_cases reject : (version != 1#u8)=true
          · try simp only [if_pos reject] at actual
            cases actual
          · try simp only [if_neg reject] at actual ⊢
            obtain ⟨padding,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
            obtain ⟨iter,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
            obtain ⟨headerResult,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
            rw [called]
            simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
            rcases headerResult with ⟨badHeader,iterOut⟩
            simp only [Aeneas.Std.uncurry] at actual ⊢
            by_cases reject : (badHeader)=true
            · try simp only [if_pos reject] at actual
              cases actual
            · try simp only [if_neg reject] at actual ⊢
              obtain ⟨end1,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨proofHashBytes,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨proofParts,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨proofDigest,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              obtain ⟨badProof,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
              rw [called]
              simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
              by_cases reject : (badProof)=true
              · try simp only [if_pos reject] at actual
                cases actual
              · try simp only [if_neg reject] at actual ⊢
                obtain ⟨pubHashBytes,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                rw [called]
                simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                obtain ⟨pubParts,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                rw [called]
                simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                obtain ⟨pubDigest,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                rw [called]
                simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                obtain ⟨badPub,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                rw [called]
                simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                by_cases reject : (badPub)=true
                · try simp only [if_pos reject] at actual
                  cases actual
                · try simp only [if_neg reject] at actual ⊢
                  obtain ⟨s6,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨domain,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨body,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨checkParts,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨a2,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  rw [called]
                  simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
                  obtain ⟨result,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
                  cases result with
                  | Err e => cases actual
                  | Ok pair =>
                    rcases pair with ⟨p1,a1⟩
                    have reference := Port6CK_Tail.accepted reserved unwrap unwrap_ok bytes length
                      nextByte end1 s6 a2 p1 a1 called
                    dsimp only [CheckpointBytes4Ops.ops] at reference
                    rw [reference]
                    exact actual

#print axioms tail_same
#print axioms current_source
#print axioms reference_source
#print axioms size_s2
#print axioms accepted
end AspisR1.Port6CK_Header
end
