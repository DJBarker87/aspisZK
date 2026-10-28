import R1Z.PV_RDEA_JoinConsumer
import R1Z.PV_RDEA_LiteralSites
import R1Z.PV_RDEA_PublicPush
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_V178ConsumedLaw
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

/-- Restated clone-first row law combines the concrete consumer with the
public request-order word; failure is an allowed prefix, with the complete
post-world retained by the consumer. No fresh-output allocator world is used. -/
theorem consumed {S F R : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F)
    (failure : PV_RDB1_V183_ReserveWorld.Error → World S F → R)
    (next : List U8 → World S F → R) :
    let e := sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w
    PV_RDEA_JoinConsumer.consume e failure next =
      (match e.1 with
       | .error err => failure err e.2
       | .ok _ => next (PV_RDEA_PushValues.value base path absolute needSep) e.2) ∧
      PV_RDEA_PrefixWords.Prefix (sizes e.2.history)
        (sizes w.history++PV_RDEA_PathSchedule.joinWord base.length path.length absolute needSep) := by
  exact ⟨PV_RDEA_JoinConsumer.endpoint step shape address absolute needSep base path w failure next,
    PV_RDEA_JoinRequests.join_requests_prefix step shape width address absolute needSep base path w⟩

#print axioms consumed
end R1Z.PV_RDEA_V178ConsumedLaw
