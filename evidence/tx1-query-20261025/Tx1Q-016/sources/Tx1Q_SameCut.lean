import Tx1Q_Execution
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_SameCut
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2W_NativeConsolidation

def dictionary {CoreError : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) : Ops :=
  Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))

def callerDigest {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  NativeBuffers.callerDigest adapterOps (withValues (dictionary ops reserved query geo)) nativeValues
    AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install std B)

attribute [local irreducible] Tx1Q_Execution.actual verifier.candidate.tx1 verifier.candidate.prepare

theorem reached {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps (dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s) :
    Nonempty (Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std) reserved query geo
      (callerDigest adapterOps ops reserved query geo B std) () (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved) := by
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (dictionary ops reserved query geo) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (ClaimsUnrolledSdk.sdkOps adapterOps (dictionary ops reserved query geo) B std)
      f.semantic f.pub f.proof f.split saved cuts.first)
  apply Tx1Q_Execution.accepted_generic
    (Tx1Q_Execution.actual ops reserved query geo B std) reserved query geo
    (callerDigest adapterOps ops reserved query geo B std) () (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved
    (Tx1Q_Execution.actual_slots ops reserved query geo B std)
  exact tx

#print axioms reached
end AspisR1.Tx1Q_SameCut
end
