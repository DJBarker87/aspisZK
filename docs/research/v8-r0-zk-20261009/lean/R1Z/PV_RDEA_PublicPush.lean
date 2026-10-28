import R1Z.PV_RDEA_PushRequests
import R1Z.PV_RDEA_PushSuccessRequests
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PublicPush
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

/-- Push does not clone. For the diagnostic/debuglink sites the public
header supplies the current length/capacity, not a fictitious clone header. -/
theorem request_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (absolute needSep : Bool)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    PV_RDEA_PrefixWords.Prefix
      (sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) absolute needSep b path w).2.history)
      (sizes w.history++PV_RDEA_PathBranches.pushWord ⟨b.values.length,b.capacity⟩ path.length absolute needSep) :=
  PV_RDEA_PushRequests.push_requests_prefix step shape width absolute needSep b path w

/-- Different path bytes with equal public length and branch predicates have
the same planned request sequence; failure may stop at an earlier prefix under
runtime/allocator primitive adequacy. -/
theorem public_word (h : PV_RDEA_PathSchedule.Header) (p q : List U8)
    (same : p.length=q.length) (absolute needSep : Bool) :
    PV_RDEA_PathBranches.pushWord h p.length absolute needSep=
      PV_RDEA_PathBranches.pushWord h q.length absolute needSep := by rw [same]

#print axioms request_prefix
#print axioms public_word
end R1Z.PV_RDEA_PublicPush
