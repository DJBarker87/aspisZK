import R1Z.PV_RunJoin_CapturedTransport60
import R1Z.PV_RunJoin_CaptureFactorSource60
import R1Z.PV_RunJoin_ProducedCallback60
import R1Z.PV_RunJoin_NativeControlSource55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeOriginalPublication60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_ResultRelation55
open PV_RunJoin_NativeControl55 (Phase)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (links : @PV_RunJoin_PublishProduced60.Links (types base) (selected base heap box ops))
    {T : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@PV_RunJoin_NativePublication55.actual (types base) (selected base heap box ops) T store)
      (@PV_RunJoin_NativePublication55.published (types base) (selected base heap box ops) T
        (@PV_RunJoin_ActualRun.data (types base) (selected base heap box ops))
        (@PV_RunJoin_ActualRun.plans (types base) (selected base heap box ops)) store) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro input
  have f := PV_RunJoin_CaptureFactorSource60.complete PV_RunJoin_NativeControl55.source store input
  have g := PV_RunJoin_CaptureFactorSource60.complete
    (PV_RunJoin_NativeCallback55.model PV_RunJoin_ActualRun.data PV_RunJoin_ActualRun.plans) store input
  have transport : Rel (PV_RunJoin_NativeResult55.Output
      (fun proof pub => PV_RunJoin_NativeCallback55.decode proof=PV_RJ4IDB.PublicationInput.publish_compact pub))
      (PV_RunJoin_NativePublication55.execute store input)
      (PV_RunJoin_NativePublication55.modelExecute PV_RunJoin_ActualRun.data PV_RunJoin_ActualRun.plans store input) := by
    unfold PV_RunJoin_NativePublication55.execute PV_RunJoin_NativePublication55.modelExecute
    rw [PV_RunJoin_NativeControlSource55.complete]
    unfold PV_RunJoin_CaptureFactorRelation60.Rel at f g
    rw [f,g]
    apply PV_RunJoin_CapturedTransport60.complete
    intro p audit next hp
    exact PV_RunJoin_ProducedCallback60.complete base heap box ops links p ⟨T,store,input,audit,next,hp⟩
  exact PV_RunJoin_NativeProjection55.complete PV_RunJoin_NativeCallback55.decode
    PV_RJ4IDB.PublicationInput.publish_compact _ _ transport

#print axioms complete
end R1Z.PV_RunJoin_NativeOriginalPublication60
