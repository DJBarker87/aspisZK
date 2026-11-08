import PV_STX2_Source7QUniformMallocRelation
import PV_STX2_Source7QUniformPreludeFrame
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7QUniformResourceHandler
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_EVHB_OWNER
open PV_STX2_Source7QUniformReceiverFrame
/-- Conditional on owner acceptance of the translator patch. The old machine
has not minted LOCAL8. Retaining its next id makes the interpretation select
ordinary allocation there and counted allocation after the source mint. -/
def Related (id : Nat) (h : PV_EVHB_RawVecOwner.Header) (w u : OWNER) : Prop :=
  R id h w u ∧ w.next = id
/-- Conditional on owner acceptance of the translator patch. Lift every native
fallback reply with its exact backend/events and preserve source registrations. -/
def lift (fallback : PV_STX2_Native.Request Data → PV_STX_World.World →
    Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  let r := fallback request (world w)
  ⟨r.answer,PV_EVHB_OwnerMachine.withWorld w r.world,r.events⟩
/-- Conditional on owner acceptance of the translator patch. Ordinary native
malloc, with source-minted owner id and M31 layout, before the OWNER hook is
installed. Other requests keep the complete native fallback reply. -/
def ordinary (resources : Resources) (encode : Encode) (id : Nat)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match request with
  | .child f _ [.number bytes,.number 4] =>
    if PV_STX2_ChainCaptures.regular f = some 65 ∧ 4 ≤ bytes then
      PV_STX2_Source7QAllocationReply.checked
        (PV_STX2_Source7QUniformMallocRelation.adopt w
          (PV_STX2_Source7QUniformOrdinaryMalloc.reply resources encode id bytes
            PV_STX2_Source7QRegisteredCut.header (world w)))
    else fallback request w
  | _ => fallback request w
/-- Conditional on owner acceptance of the translator patch. One interpretation
is installed from entry in both machines. The next-id selects the source mint
phase; the counted arm still resolves LOCAL8's actual registered id by name.
No world or registration is replaced at the resource boundary. -/
def handler (resources : Resources) (encode : Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_STX2_Native.Request Data → PV_STX_World.World →
      Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Data) :
    PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  PV_STX2_Source7QPreludeWorld.handler external (fun request w =>
    if w.next = s.next then ordinary resources encode s.next (lift fallback) request w
    else PV_STX2_Source7QAllocationReply.handler resources encode (lift fallback) entry request w)
/-- Conditional on owner acceptance of the translator patch. The actual malloc
request under the SAME installed interpretation is simulated by R plus the
unminted native next-id. This is an internal step obligation, not a new endpoint. -/
theorem malloc (resources : Resources) (encode : Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_STX2_Native.Request Data → PV_STX_World.World →
      Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Data)
    (activation bytes : Nat) (positive : 4 ≤ bytes) (w u : OWNER)
    (related : Related s.next PV_STX2_Source7QRegisteredCut.header w u) :
    let request := PV_STX2_Native.Request.child PV_STX2_Source7QAllocationReply.callee activation [.number bytes,.number 4]
    let old := handler resources encode entry external fallback request w
    let new := handler resources encode entry external fallback request u
    new.answer = old.answer ∧ new.events = old.events ∧ R s.next PV_STX2_Source7QRegisteredCut.header old.world new.world := by
  dsimp only [handler,PV_STX2_Source7QPreludeWorld.handler]
  have newNext : u.next ≠ s.next := by rw [related.1.2.next]; omega
  have regular : PV_STX2_ChainCaptures.regular PV_STX2_Source7QAllocationReply.callee = some 65 := rfl
  simp only [related.2,ite_true,newNext,ite_false,ordinary,
    PV_STX2_Source7QAllocationReply.handler,regular,positive,and_self,
    PV_STX2_Source7QUniformMallocFrame.selected resources encode entry bytes s.next
      PV_STX2_Source7QRegisteredCut.header u related.1.2]
  exact PV_STX2_Source7QUniformMallocRelation.resource resources encode s.next bytes
    PV_STX2_Source7QRegisteredCut.header w u related.1
#print axioms Related
#print axioms lift
#print axioms ordinary
#print axioms handler
#print axioms malloc
end PV_STX2_Source7QUniformResourceHandler
