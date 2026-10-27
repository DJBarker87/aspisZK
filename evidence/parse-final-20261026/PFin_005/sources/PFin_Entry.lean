import PFin_Prepared
import S2W_ChildJoins
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PFin_Entry
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) H)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val)) : S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof := by
  obtain ⟨run⟩ := Tx1Q_SameCut.reached adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts
  obtain ⟨i,p,q,source,physical,stored,parser,aligned,queries,found,read,decoded,prepare⟩ :=
    PFin_Prepared.from_cut adapter ops reserved query geo B std
      accounts1 accounts2 saved f s cuts selected run header H backend w canonical
  exact ⟨⟨_,p,parser⟩⟩

#print axioms from_cut
end AspisR1.PFin_Entry
end
