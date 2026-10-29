import R1Z.PV_RunJoin_NativeS2Source60
import R1Z.PV_RunJoin_PublishProduced60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeProducedPublication60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes] [ExternalFuns]

/-- The same source-outcome guard as the proof-slice interface. Successful
proof bytes are never read to construct model bytes. Prefix capture supplies
the actual Data/Plan index; all bytes come from the independent assembly. -/
def published {T : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (input : PV_RunJoin_NativePublication55.Input T) : Option PV_RJ4IDB.PublicationInput :=
  match PV_RunJoin_NativePublication55.execute store input with
  | .ok (.Ok _,_) =>
    match PV_RunJoin_NativeControl55.run capture store input.public1 input.compiled .S2 input.hash
        input.context input.binding input.attempt input.store with
    | .ok (.Ok (p,_),_) =>
      (exceptBytes (assembly (PV_RunJoin_ActualRun.runs p))).map (publication (PV_RunJoin_ActualRun.runs p))
    | _ => none
  | _ => none

/-- Exactly the typed native caller input; it assumes only links on captured
actual phases, and includes every source failure in the original observation. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (links : @PV_RunJoin_PublishProduced60.Links (types base) (selected base heap box ops))
    {T : Type} (store : @aspis_prover.state_only_hiding.StateOnlyMaskNonceStore (types base) T) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@PV_RunJoin_NativePublication55.actual (types base) (selected base heap box ops) T store)
      (@published (types base) (selected base heap box ops) T store) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨r24,common,backend,finish,context,range,query,node,ordering⟩ := links
  have typed := PV_RunJoin_PublishProduced60.complete base heap box ops
    r24 common backend finish context range query node ordering
  intro input
  cases hs : PV_RunJoin_NativePublication55.execute store input with
  | fail e => simp only [PV_RunJoin_NativePublication55.actual,PV_RunJoin_NativeProjection55.observe,published,hs,Option.map_none]
  | div => simp only [PV_RunJoin_NativePublication55.actual,PV_RunJoin_NativeProjection55.observe,published,hs,Option.map_none]
  | ok result =>
    rcases result with ⟨status,next⟩
    cases status with
    | Err e => simp only [PV_RunJoin_NativePublication55.actual,PV_RunJoin_NativeProjection55.observe,published,hs,Option.map_none]
    | Ok pair =>
      rcases pair with ⟨proof,audit⟩
      have hrun := hs
      rw [PV_RunJoin_NativeS2Source60.execute] at hrun
      obtain ⟨p,hcapture,hcallback⟩ := PV_RunJoin_CaptureSource60.complete
        PV_RunJoin_NativeS2Source60.callback store input proof audit next hrun
      have hp : PV_RunJoin_ActualProvenance60.Produced p := ⟨T,store,input,audit,next,hcapture⟩
      have local := typed ⟨p,hp⟩
      change resultBytes (PV_RunJoin_NativeS2Source60.callback p)=_
        at local
      change source (PV_RunJoin_ActualRun.runs p)=ok (.Ok proof) at hcallback
      change resultBytes (source (PV_RunJoin_ActualRun.runs p))=
        Option.map PV_RJ4IDB.PublicationInput.publish_compact
          (PV_RunJoin_PublishSkeleton54.published PV_RunJoin_ActualRun.runs p) at local
      simpa only [PV_RunJoin_NativePublication55.actual,PV_RunJoin_NativeProjection55.observe,
        PV_RunJoin_NativeCallback55.decode,published,hs,hcapture,
        PV_RunJoin_PublishSkeleton54.published,hcallback,resultBytes] using local

#print axioms published
#print axioms complete
end R1Z.PV_RunJoin_NativeProducedPublication60
