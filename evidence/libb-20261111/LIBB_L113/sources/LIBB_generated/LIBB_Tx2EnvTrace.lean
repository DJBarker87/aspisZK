import LIBB_Tx2EnvCode
import LIBB_V2Carriers
import LIBB_C04StoppedTrace
import LIBB_ResumeTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2EnvTrace
open Aeneas Aeneas.Std AspisR1
/-- Pure source-event expansion. Native records are never used to define
this model: resume and C04 are evaluated at their explicit source arguments. -/
def event (env : RSL.Env) : NJU_CommonObserved.Event → List RSL.Event
 | .resume ck proof pub _ =>
   NNC_ResumeEvents.render (NJU_ResumeObserved.run (LIBB_Tx2Reservation.reservation env)
    (NJC_ResumeCalls.digest (LIBB_PartitionEnv.digest env)) ck proof pub .S2 ()).events
 | .merkle pr p folded _ =>
   LIBB_C04LogGraph.render (NLP_C04Chronology.atEvent (LIBB_PartitionEnv.H env) (.merkle pr p folded .div))
 | _ => []

def common (env : RSL.Env) (pub proof ck : Slice U8) : List RSL.Event :=
 (LIBB_Tx2EnvCode.observed env pub proof ck).events.flatMap (event env)
def events (env : RSL.Env) (pub proof ck : Slice U8) : List RSL.Event :=
 match NLE_ParseInstall.parse proof with
 | .ok (.Ok _) => common env pub proof ck
 | _ => []

/-- Literal graph of the deterministic resolved source model. This is not
installed as tx2auth until stopped prefixes and the F1 gate are discharged. -/
def observation (env : RSL.Env) (pub proof ck : Slice U8) : RSL.Obs (Except LIB_ErrorDebug.VErr Unit) :=
 LIB_Carriers.resultObs (fun r => match r with | .Ok () => .ok () | .Err e => .error e)
  (events env pub proof ck) (LIBB_Tx2EnvCode.code env pub proof ck)

theorem no_write_event (env : RSL.Env) (e : NJU_CommonObserved.Event) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ event env e := by
 cases e with
 | resume ck proof pub reply => exact NNC_ResumeEvents.no_write _ _ _
 | powers gamma reply => exact List.not_mem_nil
 | inactive data reply => exact List.not_mem_nil
 | geometry queries next reply => exact List.not_mem_nil
 | pending weights reply => exact List.not_mem_nil
 | query proof p a g geometry pending reply => exact List.not_mem_nil
 | flush pending weights reply => exact List.not_mem_nil
 | finish v p a reply => exact List.not_mem_nil
 | merkle pr p folded reply =>
   intro member
   obtain ⟨q,_,equal⟩ := List.mem_map.mp member
   cases equal

theorem no_write (env : RSL.Env) (pub proof ck : Slice U8) (cell : Nat) (bytes : RSL.Bytes) :
 RSL.Event.write cell bytes ∉ events env pub proof ck := by
 unfold events
 cases h : NLE_ParseInstall.parse proof with
 | fail e => exact List.not_mem_nil
 | div => exact List.not_mem_nil
 | ok reply =>
   cases reply with
   | Err e => exact List.not_mem_nil
   | Ok variant =>
     intro member
     obtain ⟨e,_,he⟩ := List.mem_flatMap.mp member
     exact no_write_event env e cell bytes he

#print axioms no_write_event
#print axioms no_write
end LIBB_Tx2EnvTrace
end
