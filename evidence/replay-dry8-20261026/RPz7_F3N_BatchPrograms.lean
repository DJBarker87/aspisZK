import RPz7_F3N_BatchCode
import RPz7_DrvC_FirstBatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_BatchPrograms
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem errors : Op5T_Install.stageError=Port3_CheckpointInstall.error := by
  funext e
  cases e <;> rfl

theorem code_eq (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (proof : Slice U8)
    (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.stageCode hashv proof p root=Port9OR_Installed.code D () proof p root 1#usize := by
  unfold SdkC_BatchSource.stageCode
  rw [F3N_BatchCode.raw (SdkC_Source.dictionary hashv) (VTop_Checkpoint.digest D)]
  rw [errors]
  rfl

theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (total : ∀ parts,∃ digest,D.digest () parts=ok digest)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_Oracle.program (SdkC_BatchSource.stageCode hashv proof p root)=
      Port9OR_Installed.batch D () proof p root 1#usize := by
  rw [code_eq]
  exact F3N_ProgramCarrier.total (VTop_Checkpoint.digest D) () total _

theorem map_log {Err : Type} (f : AspisR1Stage2.verifier.Error → Err)
    (body : SdkC_Source.Code (core.result.Result Unit AspisR1Stage2.verifier.Error))
    (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (SdkC_BatchSource.mapCode f body))).1=
      (eval H (SdkC_Oracle.program body)).1 := by
  rw [DrvC_FirstBatch.sourceMap,DrvC_Program.program_map,DrvC_Program.eval_map]

#print axioms errors
#print axioms code_eq
#print axioms stage
#print axioms map_log
end AspisR1.F3N_BatchPrograms
end
