import F3N_BatchPrograms
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BatchSyntax
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize) :
    (eval H (SdkC_Oracle.program (SdkC_BatchSource.stageCode hashv proof p root))).1=
      (eval H (SdkC_Oracle.program (Port9OR_Batch.code Port4B_Install.leaves D () proof p root 1#usize))).1 := by
  unfold SdkC_BatchSource.stageCode
  rw [F3N_BatchPrograms.map_log,F3N_BatchCode.raw (SdkC_Source.dictionary hashv) D]

theorem current (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize) :
    (eval H (SdkC_Oracle.program (SdkC_BatchSource.currentCode hashv proof p root))).1=
      (eval H (SdkC_Oracle.program (Port9OR_Batch.code Port4B_Install.leaves D () proof
        (Tx1Q_Carriers.prepared p) root 0#usize))).1 := by
  unfold SdkC_BatchSource.currentCode
  rw [F3N_BatchPrograms.map_log]
  change (eval H (SdkC_Oracle.program (SdkC_BatchSource.code (SdkC_Source.dictionary hashv) () proof
    (Tx1Q_Carriers.prepared p).queries (Tx1Q_Carriers.prepared p).roots root 0#usize))).1=_
  rw [F3N_BatchCode.raw (SdkC_Source.dictionary hashv) D]

#print axioms stage
#print axioms current
end AspisR1.F3Q_BatchSyntax
end
