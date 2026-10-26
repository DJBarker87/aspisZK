import F3N_CurrentBatchPrograms
import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_BatchPhysical
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def fixed : VTop_Stages.aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst:={cloneInst:={clone:=fun q=>ok q}},
   digest:=fun _ _=>ok (Array.repeat 32#usize 0#u8)}

theorem total (parts : SdkC_Source.Parts) : ∃ digest,fixed.digest () parts=ok digest := ⟨_,rfl⟩

theorem stage (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (success : (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).1=ok (.Ok ())) :
    eval H (Port9OR_Installed.batch fixed () proof p root 1#usize)=
      (SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).2,
        ok (.Ok ())) := by
  have source := SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
    (SdkC_BatchSource.stageCode hashv proof p root) (.Ok ()) success
  rw [F3N_BatchPrograms.stage hashv fixed total] at source
  exact source

theorem current (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize)
    (success : (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).1=ok (.Ok ())) :
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).2=
      (eval H (Port9OR_Installed.batch fixed () proof (Tx1Q_Carriers.prepared p) root 0#usize)).1 := by
  have source := congrArg Prod.fst (SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
    (SdkC_BatchSource.currentCode hashv proof p root) (.Ok ()) success)
  exact source.symm.trans (F3N_CurrentBatchPrograms.log hashv fixed total proof p root H)

#print axioms total
#print axioms stage
#print axioms current
end AspisR1.F3N_BatchPhysical
end
