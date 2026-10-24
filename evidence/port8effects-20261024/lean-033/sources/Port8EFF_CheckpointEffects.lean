import Port8EFF_ReaderJoin
import Port6CK_Ordered
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port8EFF_CheckpointEffects
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a) | .fail e => .fail e | .div => .div

theorem mapped {A B Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (code : CheckpointBytes5Effect.Code A) (f : A → B) (H : Bytes → State) :
    eval H (Port8EFF_CheckpointCode.program D hash
      (CheckpointBytes5Effect.bind code (fun a => .done (f a))))=
      ((eval H (Port8EFF_CheckpointCode.program D hash code)).1,
        mapResult f (eval H (Port8EFF_CheckpointCode.program D hash code)).2) := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> simp only [CheckpointBytes5Effect.bind,
      Port8EFF_CheckpointCode.program,VTop_OracleCode.continueWith,eval,ih,mapResult]
  | read parts k ih => cases called : D.digest hash parts <;>
      simp only [CheckpointBytes5Effect.bind,Port8EFF_CheckpointCode.program,
        called,VTop_OracleCode.continueWith,eval,ih,mapResult]

/-- Actual installed effectful reader transports the complete CURRENT and
retained reader logs of Port6CK, with the exact same returned pair. -/
theorem reader (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (ck proof pub : Slice U8) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (actual : (eval H (Port8EFF_Bodies.reader reserved unwrap D ck proof pub .S2 hash)).2=ok (.Ok (p,a))) :
    ∃ after,
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      eval H (Port8EFF_Bodies.reader reserved unwrap D ck proof pub .S2 hash)=
        (CheckpointBytes5Inputs.observe after,ok (.Ok (p,a))) := by
  rw [Port8EFF_Bodies.reader_value] at actual
  obtain ⟨after,current,retained⟩ := Port6CK_Reader.runs reserved unwrap unwrap_ok D hash ck proof pub p a [] actual
  have pair := Port8EFF_CheckpointCode.effects (VTop_Checkpoint.digest D) hash
    (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2)
    H oracle (.Ok (p,a)) [] after current
  have full : eval H (Port8EFF_CheckpointCode.program (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2))=
        (CheckpointBytes5Inputs.observe after,ok (.Ok (p,a))) := Prod.ext pair.1.symm pair.2
  refine ⟨after,current,retained,?_⟩
  unfold Port8EFF_Bodies.reader Port8EFF_Bodies.readerCode
  rw [mapped,Port8EFF_ReaderJoin.program (Port6CK_Ops.ops reserved unwrap)
    (Port6CK_Reader.size_bound reserved unwrap),full]
  rfl

#print axioms mapped
#print axioms reader
end AspisR1.Port8EFF_CheckpointEffects
end
