import FIr_PhysicalInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_NativeInitial
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun R0P.Mask AspisV8R19.DuplexFrames

theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some p)
    (view : LiteralOpeningView.View) (claim : LiteralSemanticPrefix.E)
    (polys : Fin 10 → Polynomial LiteralSemanticPrefix.E)
    (opening : LiteralOpeningView.read (typedRows p q tr)=some view)
    (claimRead : claimOf (SelectedSemanticPrefixFacts.lift view.semantic)=some claim)
    (polyRead : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=some polys) :
    (polys 0).eval 0+(polys 0).eval 1=claim := by
  exact FIr_PhysicalInitial.on_run ops reserved query geo B std D hash pub publicBytes proof split saved run p q tr parsed view claim polys opening claimRead polyRead

#print axioms on_run
end AspisR1.FJu_NativeInitial
end
