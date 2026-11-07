import PV_STX2_ToVecCopyCallerReady
import PV_STX2_ToVecZeroOriginalOwned
import PV_STX2_ToVecCallNumberedEntry
import PV_STX2_ToVecCallCallerPost
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_STX2_ToVecCallSummary
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner

/-- The supplied machine is used directly, including its resolver and handler. -/
structure Machine where
  carrier : Carrier OWNER Data
  control : Control
  programs : Data → Option PV_STX2_SliceSyntax.Program
  handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data

/-- Required interpretations of the emitted operations and leaves. These are
machine equations, not an execution, successful-reply, or callee-Post premise.
The carrier includes the zero-capacity representation repair. -/
structure MachineSpec (m : Machine) (base : Carrier PV_STX_World.World Data)
    (ctrl : Control) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend) : Prop where
  carrier : m.carrier = PV_STX2_ToVecZeroCallCarrier.C base ctrl m.handler
  control : m.control = PV_STX2_ToVecZeroCallCarrier.control ctrl
  programs : m.programs = PV_STX2_Source7QAllocationDispatch.dispatch PV_STX2_SlicePrograms.dispatch
  leaves : m.handler = PV_STX2_Source7QPreludeWorld.handler external
    (PV_STX2_Source7QRuntimePartsReply.handler (PV_STX2_Source7QUniformResourceHandler.lift backend))
  zero_cast : PV_STX2_ToVecZeroPrepare.PV_STX2_OperatorSemantics_1291 m.carrier

/-- Call-entry data, with no constraint on the contents of the lower frames.
The allocator is the emitted Global value, shared by all source7 columns. -/
structure Entry where
  store : Store Data
  parents : List Frame
  caller : Nat
  pointer : Address
  length : Nat
  owner : OWNER
  prior : List PV_RJ4IDB.NativeEvent
  region : Vec PV_OWN2_Codec.M31
  sourceId : Nat
  sourceHeader : Header

abbrev start (e : Entry) : Config :=
  PV_STX2_ToVecCallRuntimeState.start e.store e.parents e.caller e.pointer e.length
    PV_STX2_Source7GlobalClone.value

/-- Reference-valid ownership and live numbering are entry invariants. The
usize clause is the representation bound on the source slice's length. -/
structure Pre (e : Entry) : Prop where
  argument : PV_STX2_ToVecCallReferenceEntry.Pre e.owner e.store e.pointer e.length
    e.region e.sourceId e.sourceHeader
  numbered : PV_STX2_LiveNumbering.Numbered (start e)
  usize : e.length < PV_STX2_Source7CapacityScalars.modulus

def execution (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) : Prefix OWNER PV_RJ4IDB.NativeEvent :=
  PV_STX2_ToVecZeroAdvance.advance resources encode m.carrier m.control m.programs m.handler
    fuel ⟨.running (start e),e.owner,e.prior⟩

/-- A pending answer is recorded AFTER its actual reply transition, including
that transition's world and events. Merely reaching a request is insufficient. -/
def Pending (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) (out : Prefix OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  ∃ k c w events waiting,
    fuel = k+1 ∧ execution resources encode m e k = ⟨.running c,w,events⟩ ∧
    c.frame.waiting = some waiting ∧
    (PV_STX2_Source7IterationHandler.handler resources encode c m.handler waiting.request w).answer = .pending ∧
    out = execution resources encode m e (k+1)

/-- Own completion, a fault, or an actual pending answer. No boundary follows
failure/divergence administration into a lower caller frame. -/
def Boundary (resources : Resources) (encode : Encode) (m : Machine) (e : Entry)
    (fuel : Nat) (out : Prefix OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  match out.status with
  | .undefined _ _ | .returned _ _ => False
  | .fault _ _ => True
  | .running c =>
    (c.frame.activation = (start e).frame.activation ∧ c.callers = (start e).callers ∧
      ∃ result, c.frame.completed = some result) ∨
    Pending resources encode m e fuel out

/-- The successful value, fresh identity, ownership bundle, byte copy and
entry-region frame all refer to the actual completion prefix. -/
structure Success (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (e : Entry)
    (out : Prefix OWNER PV_RJ4IDB.NativeEvent) (value : Data) : Prop where
  vector : ∃ inner, value = PV_STX2_SliceToVecConstruct.vector inner
  owned : ∃ id h,
    e.owner.next ≤ id ∧
    receiver out.world (PV_STX2_Source7QBinding.ownerPlace ⟨(start e).frame.activation,0,[]⟩) = some (id,h) ∧
    h.len = e.length ∧ h.cap = e.length ∧
    PV_OWN2_ExportContracts.VecOwnership (Attr := Unit) (Data := Data) (Native := Unit)
      (IoError := Unit) (OsString := Unit) (Scope := Unit) resources encode granted out.world
      e.region (PV_STX2_Source7QBinding.ownerPlace ⟨(start e).frame.activation,0,[]⟩)
      e.sourceId id e.sourceHeader h ∧
    (∀ offset, offset < e.length*4 →
      out.world.world.memory (h.pointer+offset) = e.owner.world.memory (e.sourceHeader.pointer+offset))
  sourceBytes : ∀ offset, offset < e.length*4 →
    out.world.world.memory (e.sourceHeader.pointer+offset) =
      e.owner.world.memory (e.sourceHeader.pointer+offset)

/-- Exact execution prefix, complete reply boundary, explicit caller-cell and
OWNER frames, and the success ownership relation. No counter identity crosses
a callee boundary; only the live-numbering invariant is required. -/
def Post (resources : Resources) (encode : Encode)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (m : Machine) (e : Entry) : Prop :=
  ∃ fuel out,
    out = execution resources encode m e fuel ∧
    Boundary resources encode m e fuel out ∧
    (∀ k, k < fuel → ¬ Boundary resources encode m e k (execution resources encode m e k)) ∧
    (∃ suffix, out.events = e.prior ++ suffix) ∧
    (∀ q : Address, q.activation < (start e).frame.activation →
      (PV_STX2_ToVecCallCallerPost.statusStore out.status).cells q = (start e).store.cells q) ∧
    (∀ q id, e.owner.places q = some id → out.world.places q = e.owner.places q) ∧
    (∀ q id, e.owner.places q = some id → lookup out.world.world id = lookup e.owner.world id) ∧
    PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed out.world
      (PV_STX2_ToVecCallCallerPost.statusStore out.status).nextActivation ∧
    (∀ c, out.status = .running c → PV_STX2_LiveNumbering.Numbered c) ∧
    (∀ c value, out.status = .running c → c.frame.completed = some (.ok value) →
      Success resources encode granted e out value)

#print Pre
#print MachineSpec
#print Post
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
end PV_STX2_ToVecCallSummary
