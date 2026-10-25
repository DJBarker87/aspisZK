import Port9OR_Bodies
import Port8EFF_CheckpointEffects

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Bridge
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- This is pointwise reuse of historical conditional facts, NOT a Program
selected using H, and NOT a comparison of two independently sampled laws. -/
theorem historical_at_native {A Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (code : CheckpointBytes5Effect.Code A) (H : Bytes → State) :
    eval H (Port9OR_Code.program D hash code)=
      eval H (Port8EFF_CheckpointCode.program (Port9OR_Code.native D H) hash code) := by
  induction code with
  | done a => rfl
  | step r k ih => cases r <;> simp only [Port9OR_Code.program,
      Port8EFF_CheckpointCode.program,VTop_OracleCode.continueWith,eval,ih]
  | read parts k ih => cases call : D.digest hash parts <;>
      simp only [Port9OR_Code.program,Port8EFF_CheckpointCode.program,Port9OR_Code.native,
        call,VTop_OracleCode.continueWith,eval,ih]

theorem reader_at_native (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant)
    (hash : Hash) (H : Bytes → State) :
    eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub v hash)=
      eval H (Port8EFF_Bodies.reader reserved unwrap (Port9OR_Bodies.native D H) ck proof pub v hash) :=
  historical_at_native _ _ _ _

theorem reader_success (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant)
    (hash : Hash) (H : Bytes → State)
    (out : core.result.Result (VTop_Stages.verifier.Prepared × VTop_Stages.verifier.Accumulator) VTop_Stages.verifier.Error)
    (actual : (eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub v hash)).2=ok out) :
    ∃ after, CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash
      (Port8EFF_Bodies.readerCode reserved unwrap ck proof pub v) []=ok (out,after) ∧
      eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub v hash)=
        (CheckpointBytes5Inputs.observe after,ok out) := by
  have nativeActual := (Port9OR_Bodies.reader_value reserved unwrap D ck proof pub v hash H).symm.trans actual
  obtain ⟨after,ran,full⟩ := Port8EFF_Bodies.reader_effects reserved unwrap
    (Port9OR_Bodies.native D H) ck proof pub v hash H (Port9OR_Code.oracle _ _ _) out nativeActual
  exact ⟨after,ran,(reader_at_native reserved unwrap D ck proof pub v hash H).trans full⟩

/-- Reuse the physical checkpoint inverse on the SAME returned pair/log.
Unwrap-on-Ok remains the inherited local primitive interpretation. -/
theorem reader_inverse (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) {Hash : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (ck proof pub : Slice U8) (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (H : Bytes → State)
    (actual : (eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub .S2 hash)).2=ok (.Ok (p,a))) :
    ∃ after,
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash
        (CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)) hash
        (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) ck proof pub .S2) []=ok (.Ok (p,a),after) ∧
      eval H (Port9OR_Bodies.reader reserved unwrap D ck proof pub .S2 hash)=
        (CheckpointBytes5Inputs.observe after,ok (.Ok (p,a))) := by
  rw [reader_at_native] at actual ⊢
  exact Port8EFF_CheckpointEffects.reader reserved unwrap unwrap_ok
    (Port9OR_Bodies.native D H) hash ck proof pub p a H (Port9OR_Code.oracle _ _ _) actual

#print axioms historical_at_native
#print axioms reader_at_native
#print axioms reader_success
#print axioms reader_inverse
end AspisR1.Port9OR_Bridge
end
