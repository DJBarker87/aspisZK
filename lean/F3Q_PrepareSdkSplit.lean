import F3Q_PrepareSplit
import AuS1_Observe
import SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PrepareSdkSplit
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem split (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepared : verifier.Prepared)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (source : ∀ h parts,D.digest h parts=hashv parts)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (semantic y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Hash),
      InstalledPreparation.sourceView proof semantic y1=ok (.Ok view) ∧
      AspisR1PublicPreparation.PreparedHashCode.erase
        (BorrowedClaimPrepared.closedPreparationCode D sem view hash input)=ok (.Ok prepared,scratch) ∧
      SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower
        (SdkD_PrepareSource.code ops B std D pub proof hash input)) []).2=
        AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
          (S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)
            D pub view.semantic hash)).1 ++
        AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
          (BorrowedClaimPrepared.closedPreparationCode D sem view hash input)).1 := by
  have erased := (SdkD_PrepareSource.source ops B std D pub proof hash input).trans success
  obtain ⟨semantic,y1,view,sem,wide,original,logs⟩ := F3Q_PrepareSplit.reached ops
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B) D pub proof hash prepared input scratch erased
  have nativeLogs := AuS1_Observe.lower hashv (SdkD_PrepareSource.code ops B std D pub proof hash input)
    (AuS1_Prepare.uniform ops B std D hashv source pub proof hash input) []
  simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at nativeLogs
  exact ⟨semantic,y1,view,sem,wide,original,nativeLogs.trans logs⟩

#print axioms split
end AspisR1.F3Q_PrepareSdkSplit
end
