import PV_STX2_Source7IterationResource
import PV_STX2_Source7QUniformInstalledHandler
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7IterationHandler
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Install the
source-stack allocator resolver at the actual configuration. All other native
requests retain the supplied complete handler, including copy and f63. This
layer performs no registration and does not replace any world. -/
def handler (resources : Resources) (encode : Encode) (c : Config)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match request with
  | .child f _ [.number bytes,.number 4] =>
    if PV_STX2_ChainCaptures.regular f = some 65 ∧ 4 ≤ bytes then
      PV_STX2_Source7IterationResource.malloc resources encode c.callers bytes w
    else fallback request w
  | _ => fallback request w
/-- Conditional on owner acceptance of the translator patch. The emitted
__rust_alloc request uses the actual saved constructor stack. No successful
answer is selected: checked retains null abort, fault, failure and pending. -/
theorem malloc (resources : Resources) (encode : Encode) (c : Config)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (activation bytes : Nat) (positive : 4 ≤ bytes) (w : OWNER) :
    handler resources encode c fallback
      (.child PV_STX2_Source7QAllocationReply.callee activation [.number bytes,.number 4]) w =
      PV_STX2_Source7IterationResource.malloc resources encode c.callers bytes w := by
  simp only [handler,show PV_STX2_ChainCaptures.regular PV_STX2_Source7QAllocationReply.callee = some 65 from rfl,
    positive,and_self,ite_true]
/-- Conditional on owner acceptance of the translator patch. Agreement at
this named native edge with the closed interpreter after source registration.
The internal target equality must be derived from the concrete context trace;
it is not a hypothesis of the intended loop endpoint. -/
theorem malloc_agreement (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (resources : Resources) (encode : Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_STX2_Native.Request Data → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Data)
    (c : Config) (activation bytes : Nat) (positive : 4 ≤ bytes) (w : OWNER)
    (minted : w.next ≠ s.next)
    (same : PV_STX2_Source7QUniformBindings.target c.callers = PV_STX2_Source7QAllocationReply.target entry) :
    let H := PV_STX2_Source7QUniformInstalledHandler.handler base ctrl resources encode entry external fallback
    handler resources encode c H
      (.child PV_STX2_Source7QAllocationReply.callee activation [.number bytes,.number 4]) w =
      H (.child PV_STX2_Source7QAllocationReply.callee activation [.number bytes,.number 4]) w := by
  dsimp only
  rw [malloc resources encode c _ activation bytes positive w]
  rw [PV_STX2_Source7IterationResource.agreement resources encode entry c.callers bytes w same]
  unfold PV_STX2_Source7QUniformInstalledHandler.handler
  rw [PV_STX2_Source7QOriginalHandler.malloc]
  simp only [PV_STX2_Source7QRuntimePartsReply.handler,
    show PV_STX2_Source7QRuntimePartsReply.isParts PV_STX2_Source7QAllocationReply.callee = false from rfl,
    Bool.false_eq_true,ite_false,PV_STX2_Source7QUniformResourceHandler.handler,
    PV_STX2_Source7QPreludeWorld.handler,minted,ite_false,
    PV_STX2_Source7QAllocationReply.handler,
    show PV_STX2_ChainCaptures.regular PV_STX2_Source7QAllocationReply.callee = some 65 from rfl,
    positive,and_self,ite_true]
#print axioms handler
#print axioms malloc
#print axioms malloc_agreement
end PV_STX2_Source7IterationHandler
