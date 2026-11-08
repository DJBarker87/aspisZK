import PV_LIB_SPEC_SparseHistory
import PV_LIB_SPEC_ConcreteEntry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SuccessResources
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen
/-- Concrete malloc replies at the named three allocation sites. Selection is
by the ACTUAL ResourceRequest origin and operation, not by a future read or
an arbitrary Store effect. Other operations retain pending replies. This is
resource DATA only; it is not a successful original-entry native history. -/
def allocation {A : Type} (request : ResourceRequest A) : ResourceReply A :=
  match request.operation with
  | .malloc size =>
    let pointer :=
      if request.site.statement = 4963 ∧ size = 48 then some 4096
      else if request.site.statement = 13923 ∧ size = PV_OWN2_ClientLayout.layout.callbackSize then some 8192
      else if request.site.statement = 14756 ∧ size = 24 then some 12288
      else none
    ⟨match pointer with | some p => .returned (.ok p) | none => .pending,
      request.before.allocator,request.before.errno⟩
  | _ => ⟨.pending,request.before.allocator,request.before.errno⟩

/-- A fixed successful handler for one local14756 pre-state, used only by the
local bridge/export witness. No restriction is imposed on row contracts. -/
def initResources : Resources := fun op w =>
  match op with
  | .malloc size => ⟨if size=24 then .returned (.ok 12288) else .pending,w.allocator,w.errno⟩
  | _ => ⟨.pending,w.allocator,w.errno⟩

def callbackResources : Resources := fun op w =>
  match op with
  | .malloc size =>
    ⟨if size=PV_OWN2_ClientLayout.layout.callbackSize then .returned (.ok 8192) else .pending,w.allocator,w.errno⟩
  | _ => ⟨.pending,w.allocator,w.errno⟩

theorem packet (site : Site) (w : PV_STX_World.World) (args : List Data) (occurrence : Nat)
    (origin : site.statement = 4963) :
    (allocation (⟨site,occurrence,args,.malloc 48,w⟩ : ResourceRequest Nat)).answer = .returned (.ok 4096) := by
  simp only [allocation,origin,and_self,ite_true]

theorem callback (site : Site) (w : PV_STX_World.World) (args : List Data) (occurrence : Nat)
    (origin : site.statement = 13923) :
    (allocation (⟨site,occurrence,args,.malloc PV_OWN2_ClientLayout.layout.callbackSize,w⟩ : ResourceRequest Nat)).answer = .returned (.ok 8192) := by
  simp only [allocation,origin,show ¬ (13923=4963 ∧ PV_OWN2_ClientLayout.layout.callbackSize=48) by omega,
    if_false,and_self,ite_true]

theorem init (site : Site) (w : PV_STX_World.World) (args : List Data) (occurrence : Nat)
    (origin : site.statement = 14756) :
    (allocation (⟨site,occurrence,args,.malloc 24,w⟩ : ResourceRequest Nat)).answer = .returned (.ok 12288) := by
  simp only [allocation,origin,show ¬ (14756=4963 ∧ (24:Nat)=48) by omega,
    show ¬ (14756=13923 ∧ (24:Nat)=PV_OWN2_ClientLayout.layout.callbackSize) by omega,
    if_false,and_self,ite_true]

theorem local_init (w : PV_STX_World.World) :
    (initResources (.malloc 24) w).answer = .returned (.ok 12288) := rfl

theorem local_callback (w : PV_STX_World.World) :
    (callbackResources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) w).answer = .returned (.ok 8192) := by
  simp only [callbackResources,ite_true]

#print axioms allocation
#print axioms initResources
#print axioms callbackResources
#print axioms packet
#print axioms callback
#print axioms init
#print axioms local_init
#print axioms local_callback
end PV_LIB_SPEC_SuccessResources
