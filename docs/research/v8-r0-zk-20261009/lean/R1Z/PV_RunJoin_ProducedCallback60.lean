import R1Z.PV_RunJoin_PublishProduced60
import R1Z.PV_RunJoin_ProducedVariant60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ProducedCallback60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54 PV_RunJoin_ResultRelation55
open PV_RunJoin_NativeControl55 (Phase)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (links : @PV_RunJoin_PublishProduced60.Links (types base) (selected base heap box ops))
    (p : @Phase (types base))
    (produced : @PV_RunJoin_ActualProvenance60.Produced (types base) (selected base heap box ops) p) :
    Rel (CoreRel (fun proof pub => PV_RunJoin_NativeCallback55.decode proof=PV_RJ4IDB.PublicationInput.publish_compact pub))
      (@PV_RunJoin_NativeControl55.source (types base) (selected base heap box ops) p)
      (@PV_RunJoin_NativeCallback55.model (types base) (selected base heap box ops)
        (@PV_RunJoin_ActualRun.data (types base) (selected base heap box ops))
        (@PV_RunJoin_ActualRun.plans (types base) (selected base heap box ops)) p) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have hv := PV_RunJoin_ProducedVariant60.actual p produced
  obtain ⟨r24,common,backend,finish,context,range,query,node,ordering⟩ := links
  have typed := PV_RunJoin_PublishProduced60.complete base heap box ops
    r24 common backend finish context range query node ordering
  unfold PV_RunJoin_NativeCallback55.model
  apply PV_RunJoin_PublicationSuccess55.complete PV_RunJoin_NativeCallback55.decode
    PV_RJ4IDB.PublicationInput.publish_compact verifier.Error.Semantic
  intro proof success
  change prover.prove_from_semantics p.public1 p.variant p.hash p.backend p.sem p.salts=ok (.Ok proof) at success
  have hs : source (PV_RunJoin_ActualRun.runs p)=ok (.Ok proof) := by
    change prover.prove_from_semantics p.public1 .S2 p.hash p.backend p.sem p.salts=_
    simpa only [hv] using success
  have ht := typed ⟨p,produced⟩
  change resultBytes (source (PV_RunJoin_ActualRun.runs p))=_ at ht
  rw [hs] at ht
  exact ht

#print axioms complete
end R1Z.PV_RunJoin_ProducedCallback60
