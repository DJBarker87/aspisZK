import Port8EFF_Bodies
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_ReaderJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Symbolic decoder-tail identity; do not unfold it under effect continuations. -/
theorem tail (ops : ResumeOps) (ck : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : CheckpointBytes5Effect.Digest) :
    Port4A_NativeReader.tail ops ck v i4 end1 s6 a2=
      CheckpointBytes5Resume.tail ops ck v i4 end1 s6 a2 := rfl

/-- Complete Program equality at the current-to-retained parent normalization,
including rejection prefixes; ONLY the local size bound is used. -/
theorem program (ops : ResumeOps)
    (sizeBound : ∀ v n, ops.checkpointSize v=ok n → 32≤n.val)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (ck proof pub : Slice U8) (v : transport.Variant) :
    Port8EFF_CheckpointCode.program D hash (Port8EFF_NativeReader.program ops ck proof pub v)=
      Port8EFF_CheckpointCode.program D hash (CheckpointBytes5Resume.program ops ck proof pub v) := by
  cases size : ops.checkpointSize v with
  | fail e =>
    simp only [Port8EFF_NativeReader.program,CheckpointBytes5Resume.program,
      CheckpointBytes5Effect.liftResult,CheckpointBytes5Effect.bind,
      Port8EFF_CheckpointCode.program,size,VTop_OracleCode.continueWith]
    rfl
  | div =>
    simp only [Port8EFF_NativeReader.program,CheckpointBytes5Resume.program,
      CheckpointBytes5Effect.liftResult,CheckpointBytes5Effect.bind,
      Port8EFF_CheckpointCode.program,size,VTop_OracleCode.continueWith]
    rfl
  | ok n =>
    by_cases same : Slice.len ck=n
    · have order : (32#usize : Usize).val≤(Slice.len ck).val := by
        rw [same]; exact sizeBound v n size
      have subEq := Port4A_ReaderNormalize.checked_sub (Slice.len ck) 32#usize order
      unfold Port8EFF_NativeReader.program CheckpointBytes5Resume.program
      rw [subEq]
      rfl
    · simp only [Port8EFF_NativeReader.program,CheckpointBytes5Resume.program,
        CheckpointBytes5Effect.liftResult,CheckpointBytes5Effect.bind,
        Port8EFF_CheckpointCode.program,size,VTop_OracleCode.continueWith,
        bne_iff_ne,if_pos same]
      rfl

#print axioms tail
#print axioms program
end AspisR1.Port8EFF_ReaderJoin
end
