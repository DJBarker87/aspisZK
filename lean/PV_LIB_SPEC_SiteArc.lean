import PV_LIB_SPEC_AllocationImages
import PV_LIB_SPEC_ScopeAllocationGap
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SiteArc
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
local instance : DecidableEq Data := Classical.decEq _
inductive SiteType where | scope | packet
  deriving DecidableEq
/-- The generic f124 body erases T in its own ArcInner tag. Its DATA operand
still carries the source type. Select that exact tag, never a field-count guess. -/
def classify (payload : Data) : Option SiteType :=
  match payload with
  | .object [("thread-aggregate-kind",kind),("thread-aggregate-slots",_)] =>
    if kind=PV_THR2_ScopeData.kind then some .scope
    else if kind=PV_THR2_Source361Aggregate54.source.2.2.1 then some .packet else none
  | _ => none

def shape : SiteType → R1Z.PV_FXM_ReserveWorld.Shape
  | .scope => ⟨40,._Align1Shl3⟩
  | .packet => PV_LIB_SPEC_SparseArc.shape

/-- Thread.inner : Pin<Arc<Inner>>. Resolve the actual source reference through
Thread/Pin/Arc/NonNull; obtain the PHYSICAL base from its OWNER header. Pin's
transparent representation is a remaining source/native representation binding,
not a successful decode hypothesis in any row or endpoint. -/
def threadWord (C : Carrier OWNER Data) (w : OWNER) (thread : Data) : Option Nat := do
  let pin ← C.field thread 0
  let arc ← C.field pin 0
  let nonNull ← C.field arc 0
  let pointer ← C.field nonNull 0
  PV_LIB_SPEC_SparsePacketHandler.physical C w pointer

/-- Initial ScopeData values are source AtomicUsize(0), AtomicBool(false) and
current Thread, NOT Packet's scope/result fields. Counter wrapper kinds and
native Pin binding must be checked at the original-entry prefix. -/
def scopeWord (C : Carrier OWNER Data) (w : OWNER) (payload : Data) : Option Nat := do
  let counter ← C.field payload 0
  let counterCell ← C.field counter 0
  let .number 0 ← C.field counterCell 0 | none
  let panic ← C.field payload 1
  let panicCell ← C.field panic 0
  let .boolean false ← C.field panicCell 0 | none
  let thread ← C.field payload 2
  threadWord C w thread

def image (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (w : OWNER) (site : SiteType) (strong weak payload : Data) : Option PV_LIB_SPEC_AllocationImages.Image := do
  let sCell ← C.field strong 0
  let .number 1 ← C.field sCell 0 | none
  let wCell ← C.field weak 0
  let .number 1 ← C.field wCell 0 | none
  match site with
  | .scope => pure (PV_LIB_SPEC_AllocationImages.scope (← scopeWord C w payload))
  | .packet => pure (PV_LIB_SPEC_AllocationImages.packet
      (← PV_LIB_SPEC_SparsePacketHandler.decode C K w strong weak payload))

/-- Only image stores are changed. Resource, null/abort, registration, backing,
header, side events and attempt accounting use the named provider models. -/
def reply (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (site : SiteType) (bytes : PV_LIB_SPEC_AllocationImages.Image) :
    Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  let r := PV_THR2_PacketBoxResource.reply resources encode s w (shape site) 8
  let out := PV_THR2_PacketBoxReply.finish s w.next
    (PV_EVHB_SourceLifetimes.emptyHeader (shape site) 8) r
  match r.answer with
  | .returned (.ok p) => if p=0 then out else
      {out with world := PV_LIB_SPEC_AllocationImages.initialized p bytes out.world}
  | _ => out

def handler (C : Carrier OWNER Data) (K : PV_STX2_SliceMachine.Control)
    (resources : Resources) (encode : Encode) (s : Store Data)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) :
    Option (Reply OWNER PV_RJ4IDB.NativeEvent Data) :=
  match request with
  | .child fn a [.object [("thread-aggregate-kind",kind),
      ("thread-aggregate-slots",.array [.array [strong],.array [weak],.array [payload]])]] =>
    if fn=PV_THR2_Packet124BoxIssue17.fn ∧ a=s.nextActivation ∧
        kind=PV_THR2_Packet124Aggregate13.source.2.2.1 then
      match classify payload with
      | none => none
      | some site =>
        let r := PV_THR2_PacketBoxResource.reply resources encode s w (shape site) 8
        match r.answer with
        | .returned (.ok p) =>
          if p=0 then some (reply resources encode s w site (fun _ => none))
          else (image C K w site strong weak payload).map (reply resources encode s w site)
        | _ => some (reply resources encode s w site (fun _ => none))
    else some (fallback request w)
  | _ => some (fallback request w)

/-- Ownership/pointer laws rechecked for BOTH concrete layouts. The actual
stored-byte conclusion distinguishes copied unknown bytes from unwritten ones. -/
theorem returned_owned (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (site : SiteType) (bytes : PV_LIB_SPEC_AllocationImages.Image) (p : Nat)
    (answer : (resources (.malloc (shape site).width) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) :
    let out := reply resources encode s w site bytes
    out.answer = .returned (.ok (PV_THR2_PacketBoxReply.value s)) ∧
    OwnedAt out.world.world w.next ∧
    receiver out.world (PV_THR2_PacketBoxRegister.place s) = some (w.next,
      capacityStore (pointerStore (PV_EVHB_SourceLifetimes.emptyHeader (shape site) 8) p) 1) ∧
    (∀ i value, bytes i = some value → out.world.world.memory (p+i) = value) ∧
    (∀ address, bytes (address-p) = none → out.world.world.memory address =
      (PV_THR2_PacketBoxReply.finish s w.next
        (PV_EVHB_SourceLifetimes.emptyHeader (shape site) 8)
        (PV_THR2_PacketBoxResource.reply resources encode s w (shape site) 8)).world.world.memory address) := by
  intro out
  have ok := (PV_THR2_PacketBoxResource.answer resources encode s w (shape site) 8).trans answer
  have done := PV_THR2_PacketBoxReply.returned s w.next p
    (PV_EVHB_SourceLifetimes.emptyHeader (shape site) 8) _ ok nonnull
  have own := PV_THR2_PacketBoxResourceOwned.returned resources encode s w (shape site) 8 p answer nonnull
  have pointer := PV_THR2_PacketBoxPointerAssociation.returned resources encode s w (shape site) 8 p answer nonnull
  dsimp only [out,reply]
  simp only [ok,if_neg nonnull]
  exact ⟨by rw [done],own.2,pointer,
    fun i value store => PV_LIB_SPEC_AllocationImages.stored p i bytes _ value store,
    fun address absent => PV_LIB_SPEC_AllocationImages.hole p address bytes _ absent⟩

theorem scope_classified (counter thread panicked : Data) :
    classify (PV_THR2_ScopeData.value counter thread panicked) = some .scope := by
  simp only [classify,PV_THR2_ScopeData.value,PV_THR2_KeyValues.pack,ite_true]

theorem packet_classified (scope payload marker : Data) :
    classify (PV_THR2_KeyValues.pack PV_THR2_Source361Aggregate54.source.2.2.1 [scope,payload,marker]) = some .packet := by
  simp only [classify,PV_THR2_KeyValues.pack]
  rw [if_neg (by intro impossible; cases impossible)]
  rfl

theorem layout_distinct : (shape .scope).width = 40 ∧ (shape .packet).width = 48 := ⟨rfl,rfl⟩

#print axioms SiteType
#print axioms classify
#print axioms shape
#print axioms threadWord
#print axioms scopeWord
#print axioms image
#print axioms reply
#print axioms handler
#print axioms returned_owned
#print axioms scope_classified
#print axioms packet_classified
#print axioms layout_distinct
end PV_LIB_SPEC_SiteArc
