import PV_LIB_SPEC_SiteArc
import PV_LIB_SPEC_SparseRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SiteRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_SparseRuntime (values pureValue)
/-- Site-type allocation repair of SPEC-C6 (accepted D993). ScopeData40/8 and
Packet48/8 select their own images; all-answer resource semantics remain.
Callback and Thread::new image installation still require native-byte/source
bindings. This assembly does not claim those missing bindings or full adequacy. -/
def native (p : Parameters) (c : Config) (request : PV_STX2_Native.Request Data)
    (w : OWNER) : Option (Reply OWNER Event Data) :=
  let C := (runtime p).carrier
  let K := (runtime p).control
  let H := PV_THR2_FnOnceDispatch.handler
    (values C K (PV_THR2_OwnUniformResourceHandler.lift p.environment.native))
  let H := PV_THR2_ManuallyDropHandler.handler H
  let H := PV_THR2_IntrinsicSemantics_NonNullAsRef.handler C c.store H
  let H := PV_THR2_PacketPointerSemantics.handler H
  let H := PV_THR2_ClosureBoxActivationHandler.handler p.resources p.encode H
  match request with
  | .child _ a _ => PV_LIB_SPEC_SiteArc.handler C K p.resources p.encode
      {c.store with nextActivation := a} H request w
  | _ => some (H request w)

def invalidPure (p : Parameters) (c : Config) (w : OWNER) : Bool :=
  match c.frame.waiting with
  | some wait => match wait.request with
    | .child fn _ args =>
      match PV_THR2_OffPath.functionId fn with
      | some 121 | some 277 | some 278 | some 279 =>
        match (PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request w).answer with
        | .returned (.ok _) => (pureValue (runtime p).carrier (runtime p).control w fn args).isNone
        | _ => false
      | _ => false
    | _ => false
  | none => false

/-- Rechecked BoundRuntime value/ghost assembly. Every ordinary full answer
is framed, including failure/pending; only exact named allocation tokens may
change registry fields. Arc returned value uses the actual reached count. -/
def valueAnswer (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) := do
  let r ← native p c request w
  let r ← match request with
    | .child fn _ args =>
      if PV_THR2_OffPath.functionId fn = some 360 then
        match r.answer with
        | .returned (.ok _) => do
          let (value,count) ← PV_LIB_SPEC_BoundRuntime.arc (runtime p).carrier c.store w args
          if count > PV_THR2_LibrarySemantics_ArcClone.maxRefcount then
            some ⟨.fault .abort,w,r.events⟩
          else some ⟨.returned (.ok value),w,r.events⟩
        | _ => some r
      else if invalidPure p c w then none else some r
    | _ => some r
  pure r

def answer (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  (valueAnswer p c request w).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

def handler (p : Parameters) (c : Config) : Handler :=
  fun request w => (answer p c request w).getD
    (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)


theorem ordinary_framed (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (r : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : answer p c request w = some r) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w r.world := by
  unfold answer at result
  cases hv : valueAnswer p c request w with
  | none => rw [hv] at result; cases result
  | some original =>
    rw [hv] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w original ordinary

#print axioms native
#print axioms invalidPure
#print axioms valueAnswer
#print axioms answer
#print axioms handler
#print axioms ordinary_framed
end PV_LIB_SPEC_SiteRuntime
