import PV_LIB_SPEC_SuccessResources
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LocalOwnership
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
open PV_LIB_SPEC_SuccessResources
/-- Concrete LOCAL allocation/registration/ready data. This is deliberately
not called an original-entry history: the source prefix still has to produce
these data. It checks the export applications without any decoder premise. -/
def allocationStore : Store Data := ⟨fun _ => none,10⟩
def sourceStore : Store Data := ⟨fun _ => none,12⟩
def encode : Encode := PV_LIB_SPEC_ConcreteEntry.parameters.encode
def before : OWNER := PV_LIB_SPEC_ConcreteCaptures.state
def allocated : OWNER := (PV_THR2_ClosureBoxAllocation.reply callbackResources encode allocationStore before).world
def registered : OWNER := PV_THR2_BindingRegister.register
  ⟨{activation := 1,remaining := PV_THR2_F361.live.body.drop 113},[],sourceStore⟩ allocated
def pre : OWNER := withWorld registered (world allocated)
def handle : Pointer := ⟨16384,by decide⟩
def data : Pointer := ⟨8192,by decide⟩
def loadBias : Pointer := ⟨0,by decide⟩
def index : Fin 11 := ⟨0,by decide⟩
def payload : Data := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
  [PV_THR2_OwnInitPointerCodec.encode handle,
    PV_THR2_BoxDynRepresentationBridge.callback (PV_THR2_BoxDynBinaryLayout.symbols loadBias index)
      (PV_THR2_PacketBoxBacking.root allocationStore)]
def readyStore : Store Data := write sourceStore ⟨1,46,[]⟩ (some payload)
def ready : Config := ⟨{activation := 1,remaining := PV_THR2_F361.live.body.drop 129},[],readyStore⟩
def q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent := ⟨⟨.running ready,pre,[]⟩,[]⟩
def granted : GrantedRegions := fun _ _ base size => base=12288 ∧ size=24

theorem metadata (address : Nat) :
    pre.world.allocator.metadata address =
      if address=8192 then some (layout (PV_EVHB_SourceLifetimes.emptyHeader
        PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment) 1)
      else before.world.allocator.metadata address := by
  rfl

/-- No guessed disjointness: the concrete allocated metadata bounds every
positive owned interval below the next granted12288/24 region. -/
theorem old_range (h : Header) (owned : Owned pre.world h)
    (positive : 0<h.cap) : h.pointer+h.cap*h.shape.width ≤ 8304 := by
  rcases owned with ⟨allocationMeta,live⟩ | ⟨_,zero⟩
  · rw [metadata] at allocationMeta
    by_cases p : h.pointer=8192
    · rw [if_pos p] at allocationMeta
      have size := congrArg Allocation.bytes (Option.some.inj allocationMeta)
      change 56 = h.cap*h.shape.width at size
      omega
    · rw [if_neg p] at allocationMeta
      change (if h.pointer=112 then some (layout PV_LIB_SPEC_ConcreteCaptures.runHeader 1)
        else if h.pointer=64 then some (layout PV_LIB_SPEC_ConcreteCaptures.nHeader 1)
        else if h.pointer=104 then some (layout PV_LIB_SPEC_ConcreteCaptures.fHeader 1) else none) = _ at allocationMeta
      split at allocationMeta
      · have size := congrArg Allocation.bytes (Option.some.inj allocationMeta)
        change 16 = h.cap*h.shape.width at size
        omega
      · split at allocationMeta
        · have size := congrArg Allocation.bytes (Option.some.inj allocationMeta)
          change 8 = h.cap*h.shape.width at size
          omega
        · split at allocationMeta
          · have size := congrArg Allocation.bytes (Option.some.inj allocationMeta)
            change 0 = h.cap*h.shape.width at size
            omega
          · cases allocationMeta
  · omega

theorem fresh : FreshAllocationValidity' initResources granted pre := by
  constructor
  · intro A op pointer bytes success nonnull positive
    cases op with
    | malloc size =>
      change bytes=size ∧ (if size=24 then Answer.returned (.ok 12288) else .pending) = .returned (.ok pointer) at success
      by_cases is24 : size=24
      · rw [if_pos is24] at success
        have pointerEq : pointer=12288 := by cases success.2; rfl
        have bytesEq : bytes=24 := success.1.trans is24
        subst pointer; subst bytes
        refine ⟨⟨12288,24,⟨rfl,rfl⟩,by omega,by omega⟩,?_⟩
        intro h owned cap width
        exact Or.inl (by have bound := old_range h owned cap; omega)
      · rw [if_neg is24] at success
        cases success.2
    | calloc size count => cases success.2
    | posixMemalign align size => cases success.2
    | realloc pointer oldSize alignment newSize => cases success
    | free pointer => cases success
    | copy source target bytes => cases success
    | zero pointer bytes => cases success
  · intro w allocator base size region
    rcases region with ⟨rfl,rfl⟩
    decide

def C : Carrier OWNER Data := (PV_LIB_SPEC_Frozen.runtime PV_LIB_SPEC_ConcreteEntry.parameters).carrier
def K : Control := (PV_LIB_SPEC_Frozen.runtime PV_LIB_SPEC_ConcreteEntry.parameters).control
def P : Data → Option PV_STX2_SliceSyntax.Program := fun _ => none
def H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  fun _ w => ⟨.pending,w,[]⟩
def words : PV_OWN2_ThreadInitLayout.InitWords :=
  ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress loadBias index⟩
def allocationReply := PV_THR2_OwnInitAllocationHandlerBridged.handler initResources encode H
  (.child PV_THR2_Source361InitChildren.fnAllocationFull readyStore.nextActivation [payload]) pre
def post := PV_THR2_OwnInitInterpreterBridged.advance C K P initResources encode H
  (PV_THR2_Source361AllocationFull.steps C q) q

/-- Actual APPLICATION of allBridged at one concrete successful local source
allocation cut. Success is derived from the fixed resource data; bridge decode
is derived by allBridged, not assumed. This is not original-entry reachability
or an application of the corrected store-action machine's row contract. -/
theorem applied :
    PV_THR2_OwnInitAllocationCases.Outcome ⟨1,[45]⟩ words
      (initResources (.malloc 24) (world pre)).answer
      {allocationReply with world := post.current.world} ∧
    (∀ cid ch, receiver pre ⟨1,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) initResources encode granted
        ⟨1,[39]⟩ ⟨1,[45]⟩ cid pre.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)) := by
  exact PV_THR2_OwnInitActualAllocationOwned.allBridged C K P
    callbackResources encode allocationStore sourceStore before handle data 1 []
    (world allocated) loadBias index initResources encode granted H q ready
    (local_callback _) (by decide) rfl ⟨rfl,rfl,rfl,rfl⟩ rfl rfl rfl rfl fresh

/-- Direct application of the named ownership export. Its conditional fields
remain conditional: this does NOT discharge their whole-run source premises. -/
theorem ownership_export :
    PV_OWN2_ExportContracts.SourceOwnership
      (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
      (OsString := Unit) (Scope := Unit) initResources encode granted
      ⟨1,[39]⟩ ⟨1,[45]⟩ 4 pre.next
      (capacityStore (pointerStore (PV_EVHB_SourceLifetimes.emptyHeader
        PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment) 8192) 1)
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) :=
  PV_OWN2_Exports.SourceInitBoxOwnership initResources encode granted _ _ _ _ _ _

#print axioms allocationStore
#print axioms sourceStore
#print axioms encode
#print axioms before
#print axioms allocated
#print axioms registered
#print axioms pre
#print axioms handle
#print axioms data
#print axioms loadBias
#print axioms index
#print axioms payload
#print axioms readyStore
#print axioms ready
#print axioms q
#print axioms granted
#print axioms metadata
#print axioms old_range
#print axioms fresh
#print axioms C
#print axioms K
#print axioms P
#print axioms H
#print axioms words
#print axioms allocationReply
#print axioms post
#print axioms applied
#print axioms ownership_export
end PV_LIB_SPEC_LocalOwnership
