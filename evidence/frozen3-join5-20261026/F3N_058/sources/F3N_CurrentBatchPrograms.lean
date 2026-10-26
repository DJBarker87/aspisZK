import F3N_BatchPrograms
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_CurrentBatchPrograms
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem code_eq (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (proof : Slice U8)
    (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    SdkC_BatchSource.mapCode Op5T_Install.stageError
      (SdkC_BatchSource.code (SdkC_Source.dictionary hashv) () proof p.queries p.roots root 0#usize)=
        Port9OR_Installed.code D () proof (Tx1Q_Carriers.prepared p) root 0#usize := by
  rw [F3N_BatchPrograms.errors]
  change SdkC_BatchSource.mapCode Port3_CheckpointInstall.error
      (SdkC_BatchSource.code (SdkC_Source.dictionary hashv) () proof
        (Tx1Q_Carriers.prepared p).queries (Tx1Q_Carriers.prepared p).roots root 0#usize)=_
  rw [F3N_BatchCode.raw (SdkC_Source.dictionary hashv) (VTop_Checkpoint.digest D)]
  rfl

theorem log (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (total : ∀ parts,∃ digest,D.digest () parts=ok digest)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize)
    (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (SdkC_BatchSource.currentCode hashv proof p root))).1=
      (eval H (Port9OR_Installed.batch D () proof (Tx1Q_Carriers.prepared p) root 0#usize)).1 := by
  unfold SdkC_BatchSource.currentCode
  rw [F3N_BatchPrograms.map_log]
  rw [← F3N_ProgramCarrier.total (VTop_Checkpoint.digest D) () total]
  rw [← code_eq hashv D proof p root,F3N_BatchPrograms.map_log]

#print axioms code_eq
#print axioms log
end AspisR1.F3N_CurrentBatchPrograms
end
