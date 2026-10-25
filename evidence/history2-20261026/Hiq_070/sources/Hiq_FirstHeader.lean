import Hiq_FirstShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_FirstHeader
open Aeneas Aeneas.Std Result

/-- Marker and size come from the installed writer's own serialization. They
do not need canonical field values, a second TX, or SessionA arithmetic laws. -/
theorem decoded {C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      semantic pub proof split = ok (.Ok saved))
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.DuplexFrames.State)
    (oracle : CheckpointBytes5Inputs.Oracle
      (S2Z.Oracle.leadDigest (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)) () H) :
    CPhy_Header.decode (MultiproofConeCanonical.bytesOf saved.val) =
      some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std) _
    semantic pub proof split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      semantic pub proof split saved first)
  obtain ⟨run⟩ := Tx1Q_Execution.accepted_generic
    (Tx1Q_Execution.actual ops reserved query geo B std) reserved query geo
    (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std) ()
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split saved
    (Tx1Q_Execution.actual_slots ops reserved query geo B std) tx
  exact (CPhy_Header.writer _ () H oracle _ _ proof pub saved run.writer_call).1

#print axioms decoded
end AspisR1.Hiq_FirstHeader
end
