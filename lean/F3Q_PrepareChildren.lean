import F3Q_PrepareSdkSplit
import F3Q_PrepareMap
import AuS1_Observe
import SdkD_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_PrepareChildren
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
          (AspisR1PublicPreparation.S1SemanticCode.verify
          (AspisR1PublicPreparation.S1SemanticCode.finish AspisS1ExtractedRoundChildren.children
            (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B)))
          (InstalledPreparation.retainedDigest D) (FirstComposition.toRetainedPublic pub) view.semantic hash none)).1 ++
        AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
          (AspisR1PublicPreparation.PreparedSourceEffects.prepare
          (AspisR1PublicPreparation.PreparedHashCode.preparationEffects BorrowedClaimPrepared.closedHashBoundaries BorrowedClaimPrepared.closedHashQueries)
          (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
          (InstalledPreparation.retainedView view) hash (AspisR1ClaimPreparedBridge.mapArray InstalledPreparation.retainedE input))).1 := by
  obtain ⟨semantic,y1,view,sem,wide,original,logs⟩ := F3Q_PrepareSdkSplit.split ops B std D pub proof hash
    input scratch prepared hashv sha256 H p1 syscall source success
  rw [F3Q_PrepareMap.semantic,F3Q_PrepareMap.original] at logs
  exact ⟨semantic,y1,view,sem,wide,original,logs⟩

#print axioms split
end AspisR1.F3Q_PrepareChildren
end
