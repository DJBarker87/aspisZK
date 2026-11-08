import PV_LIB_SPEC_F361Full
import PV_LIB_SPEC_F270Full
import PV_LIB_SPEC_F166Full
import PV_LIB_SPEC_F15Full
import PV_LIB_SPEC_F208Full
import PV_LIB_SPEC_F220Full
import PV_LIB_SPEC_F316Full
import PV_LIB_SPEC_F318Full
import PV_LIB_SPEC_F219Full
import PV_LIB_SPEC_F125Full
import PV_LIB_SPEC_F6Full
import PV_LIB_SPEC_F170Full
import PV_LIB_SPEC_F17Full
import PV_LIB_SPEC_F5Full
import PV_LIB_SPEC_F2Full
import PV_LIB_SPEC_F1Full
import PV_LIB_SPEC_F0Full
import PV_LIB_SPEC_OwnInitFull
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_Frozen
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
/-- Full allocation/reservation channels: actual emitted site, dynamic
occurrence, argument values and before-world. Native full replies are separate.
These are data, never a may-abort relation or a success restriction. -/
structure ResourceRequest (A : Type) where
  site : PV_STX2_Syntax.Site
  occurrence : Nat
  arguments : List Data
  operation : PV_EVHB_GlobalSystem.Primitive A
  before : PV_STX_World.World
structure Environment where
  allocation : {A : Type} → ResourceRequest A → ResourceReply A
  reservation : {A : Type} → ResourceRequest A → ResourceReply A
  native : PV_STX2_Native.Request Data → PV_STX_World.World → Reply PV_STX_World.World Event Data
/-- Primitive runtime/ABI parameters fixed outside all entry quantifiers. The
source carrier is ASSEMBLED below by name, not supplied as a desired row model.
Resource-channel/source-request association is a separate adequacy target. -/
structure Parameters where
  primitives : Carrier OWNER Data
  control : Control
  needsDrop : Bool
  resources : Resources
  encode : Encode
  loadBias : PV_OWN2_Codec.Pointer
  siteIndex : Fin 11
  environment : Environment

def runtime (p : Parameters) : Runtime :=
  {carrier := PV_THR2_OwnInitExactReturnedCases.carrier
      (PV_THR2_OperatorSemantics_14121.carrier
        (PV_THR2_OperatorSemantics_14119.carrier
          (PV_THR2_BoxDynBinaryLayout.symbols p.loadBias p.siteIndex)
          (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
            (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier
              (PV_THR2_OperatorCarrier.carrier p.primitives)))) p.needsDrop))) p.needsDrop
   control := PV_THR2_Scalars.control (PV_THR2_ThreadFields.control p.control)
   fallback := fun _ => none
   native := PV_THR2_FnOnceDispatch.handler
      (PV_THR2_OwnUniformResourceHandler.lift p.environment.native)
   resources := p.resources,encode := p.encode}

def source (table : FullStoreActionTable) (p : Parameters) : Machine :=
  PV_LIB_SPEC_Full.source table (runtime p)
def MachineSpec (table : FullStoreActionTable) (p : Parameters) (m : Machine) : Prop :=
  PV_LIB_SPEC_Full.MachineSpec table (runtime p) m

/-- Source references to initialized STACK locals do not require an OWNER
heap registration. Registration/header validity applies to entry-REGISTERED
regions; byte codecs/registration of captured owned regions remain the row's
named provider predicates. This avoids inventing OWNER records for the actual
F2/F5 stack borrow of their LocalKey. Physical reference representation is the
named source/ABI adequacy obligation, never a future decoder hypothesis. -/
def References (r : Runtime) (i : Input) : Prop :=
  ∀ v address, Reachable r i v → r.carrier.dereference i.world v = some address →
    ∃ value, readAddress r.carrier i.store address = some value

def EntryPre (body : PV_STX2_SliceSyntax.Program) (arity : Nat)
    (p : Parameters) (i : Input) : Prop :=
  i.arguments.length = arity ∧
  (∀ n v, i.arguments[n]? = some v → i.store.cells ⟨i.activation,n+1,[]⟩ = some v) ∧
  i.parent.waiting = some i.waiting ∧
  i.waiting.action = .child i.activation (.local i.destination) ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.activation ∧
  RegisteredValidity i.world ∧ Numbered (entry body i) ∧ References (runtime p) i

def RootPre (p : Parameters) (i : PV_LIB_SPEC_F0Full.Original) : Prop :=
  i.store.cells ⟨i.activation,1,[]⟩ = some (.number i.n) ∧
  i.store.cells ⟨i.activation,2,[]⟩ = some i.closure ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.activation ∧
  RegisteredValidity i.world ∧ Numbered (PV_LIB_SPEC_F0Full.rootEntry i) ∧
  References (runtime p) (PV_LIB_SPEC_F0Full.referenceInput i) ∧
  PV_LIB_SPEC_F0Full.Captures i.world i.n i.closure

/-- Bind independently source-indexed resource requests to the primitive
allocator/reservation channels on actual source resource traces. This is an
ADEQUACY TARGET, not a MachineSpec, Pre, successful allocation or endpoint
hypothesis. `requests` is the actual child/source projection to be established. -/
def ResourceBinding (p : Parameters)
    (requests : Nat → List (Bool × (Sigma ResourceRequest))) : Prop :=
  ∀ n pair, pair ∈ requests n →
    @p.resources pair.2.1 pair.2.2.operation pair.2.2.before =
      (if pair.1 then p.environment.reservation pair.2.2 else p.environment.allocation pair.2.2)

/-- Exact common refinements of the earlier operational drafts. No implication
from these source/ABI targets is assumed merely by defining a source machine. -/
def EntryComparison (body : PV_STX2_SliceSyntax.Program) (arity : Nat)
    (p : Parameters) (i : Input) : Prop :=
  (PV_LIB_SPEC_Row.Pre body arity (runtime p) i → References (runtime p) i) ∧
  (EntryPre body arity p i → RegisteredValidity i.world ∧ Numbered (entry body i))

#print axioms Environment
#print axioms Parameters
#print axioms runtime
#print axioms source
#print axioms MachineSpec
#print axioms References
#print axioms EntryPre
#print axioms RootPre
#print axioms ResourceBinding
#print axioms EntryComparison

namespace F270
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F270.live 3 p i ∧ ∃ builder scope closure, i.arguments = [builder,scope,closure] ∧
    PV_THR2_TypedRepresentation_Builder.Shape builder
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F270.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f270.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F270

namespace F166
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F166.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F166.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f166.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F166

namespace F15
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F15.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F15.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f15.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F15

namespace F208
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F208.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F208.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f208.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F208

namespace F220
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F220.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F220.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f220.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F220

namespace F316
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F316.live 1 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F316.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f316.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F316

namespace F219
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F219.live 1 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F219.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f219.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F219

namespace F125
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F125.live 1 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F125.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f125.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F125

namespace F6
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F6.live 1 p i ∧ ∃ (F Task : Type)
    (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task) (callback : Data),
    PV_FN_THREAD_f6.Pre' (PV_LIB_SPEC_F6Full.packageInput i) captures callback
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F6.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f6.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F6

namespace F170
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F170.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F170.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f170.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F170

namespace F17
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F17.live 2 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F17.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f17.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F17

namespace F5
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F5.live 0 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F5.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f5.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F5

namespace F2
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F2.live 0 p i
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F2.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f2.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F2

namespace F1
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Complete source-entry domain; no future call or successful outcome. -/
def Pre (p : Parameters) (i : Input) : Prop := EntryPre PV_THR2_F1.live 3 p i ∧ ∃ n f flag, i.arguments = [.number n,f,flag] ∧ n < 2^64 ∧
    ∃ b, (runtime p).carrier.truth flag = some b
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F1.live i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
/-- The package target is supplied by the literal compiled comparison root
listed in SESSION5_FULL_PACKAGE_f1.json; it is not a new Contract premise. -/
def Comparison (packageTarget : Prop) (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageTarget ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F1

namespace F361
abbrev Input := PV_FN_THREAD_f361.Input
abbrev Representation := PV_LIB_SPEC_F361Full.Representation
def view (x : Input) : PV_LIB_SPEC_Row.Input :=
  ⟨x.s,x.a,[x.threadName,x.stackSize,x.noHooks,x.scope,x.captured],x.parent,x.parents,
    x.dest,x.wait,x.w,x.es,x.stack⟩
def MachineSpec (table : FullStoreActionTable) (p : Parameters) (x : Input) (m : Machine) : Prop :=
  PV_LIB_SPEC_Frozen.MachineSpec table p m ∧ PV_LIB_SPEC_F361Full.MachineSpec table x m
def Pre (p : Parameters) (R : Representation) (x : Input) : Prop :=
  PV_LIB_SPEC_F361Full.Pre R x ∧ References (runtime p) (view x)
def Post (table : FullStoreActionTable) (p : Parameters) (x : Input)
    (candidate : Nat → State) : Prop :=
  let m := source table p
  PV_LIB_SPEC_Frontier.Behavior m (PV_FN_THREAD_f361.entry x) candidate ∧
  ∀ k, (∀ j, j < k → ¬ PV_LIB_SPEC_Frontier.Boundary m (PV_FN_THREAD_f361.entry x) candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) →
      PV_FN_THREAD_f361.Frame x (candidate k) ∧ Numbered (candidate k)
def Contract (table : FullStoreActionTable) (p : Parameters) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m x, MachineSpec table p x m → Pre p R x → Post table p x (implementation m x)
abbrev PackagePre := PV_FN_THREAD_f361.Pre
abbrev PackagePost := PV_FN_THREAD_f361.Post
def Comparison (table : FullStoreActionTable) (p : Parameters) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ x, Pre p R x ↔ PV_LIB_SPEC_F361Full.Pre R x ∧ References (runtime p) (view x)) ∧
  Contract table p R implementation
#print axioms view
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackagePre
#print axioms PackagePost
#print axioms Comparison
end F361

namespace F318
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev entry := PV_LIB_SPEC_F318Full.entry
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
/-- Intrinsic entry uses its actual pending caller, not a fictional318 body. -/
def Pre (p : Parameters) (i : Input) : Prop :=
  (∃ data, i.arguments = [(PV_THR2_Catch219Callbacks.token false).2,data,
    (PV_THR2_Catch219Callbacks.token true).2]) ∧
  i.parent.waiting = some i.waiting ∧
  i.waiting.request = .child PV_THR2_Catch219Call318.fn i.activation i.arguments ∧
  i.waiting.action = .child i.activation (.local i.destination) ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  RegisteredValidity i.world ∧ Numbered (entry i) ∧ References (runtime p) i

def Boundary (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  PV_LIB_SPEC_F318Full.Delivered i (trace n) ∨ Terminal (entry i) (trace n) ∨
    ∃ k, n = k+1 ∧ PV_LIB_SPEC_Frontier.Pending m (trace k) ∧ trace n = step m (trace k)
def First (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m i trace n ∧ ∀ k, k < n → ¬ Boundary m i trace k

def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  let m := source table p
  let ref := fun n => run m n (entry i)
  ((∃ n k, First m i ref n ∧ First m i candidate k ∧
      PV_LIB_SPEC_Frontier.observe (candidate k) = PV_LIB_SPEC_Frontier.observe (ref n)) ∨
    ((∀ n, ¬ Boundary m i ref n) ∧ (∀ k, ¬ Boundary m i candidate k) ∧
      (∀ n, ∃ k, (ref n).current.events = (candidate k).current.events) ∧
      (∀ k, ∃ n, (ref n).current.events = (candidate k).current.events))) ∧
  ∀ k, (∀ j, j < k → ¬ Boundary m i candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) →
      PV_LIB_SPEC_ThreadRow.Frame (runtime p) i (candidate k)
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
def Comparison (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PV_LIB_SPEC_F318Full.PackageStatement ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Boundary
#print axioms First
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F318

namespace F0
abbrev Original := PV_LIB_SPEC_F0Full.Original
abbrev Input := PV_LIB_SPEC_F0Full.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
abbrev PreRoot := RootPre
def Pre (p : Parameters) : Input → Prop
  | .original i => RootPre p i
  | .call i => EntryPre PV_THR2_F0.live 2 p i ∧
    ∃ n closure, i.arguments = [.number n,closure] ∧ PV_LIB_SPEC_F0Full.Captures i.world n closure

def PostRoot (table : FullStoreActionTable) (p : Parameters) (i : Original)
    (candidate : Nat → State) : Prop :=
  let m := source table p
  PV_LIB_SPEC_Frontier.Behavior m (PV_LIB_SPEC_F0Full.rootEntry i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ PV_LIB_SPEC_Frontier.Boundary m (PV_LIB_SPEC_F0Full.rootEntry i) candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) →
      PV_LIB_SPEC_F0Full.RootFrame (runtime p) i (candidate k)
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  match i with
  | .original root => PostRoot table p root candidate
  | .call call => PV_LIB_SPEC_Frontier.Post table (runtime p) PV_THR2_F0.live call candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)
def Comparison (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PV_LIB_SPEC_F0Full.PackageStatement ∧ Contract table p implementation
#print axioms MachineSpec
#print axioms PreRoot
#print axioms Pre
#print axioms PostRoot
#print axioms Post
#print axioms Contract
#print axioms Comparison
end F0

namespace OwnInit
abbrev Input := PV_LIB_SPEC_OwnInitFull.Input
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec
abbrev Pre := RootPre
def representation (p : Parameters) (granted : PV_OWN2_FreshAllocation.GrantedRegions) :
    PV_LIB_SPEC_OwnInitFull.Representation := ⟨p.loadBias,p.siteIndex,granted⟩
def Post (table : FullStoreActionTable) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_OwnInitFull.Post table (runtime p) (representation p granted) i candidate
def Contract (table : FullStoreActionTable) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p granted i (implementation m i)
def Comparison (table : FullStoreActionTable) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ i, (Pre p i ∧ PV_LIB_SPEC_OwnInitFull.LegacySome table (runtime p) i) → Pre p i) ∧
  Contract table p granted implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms representation
#print axioms Post
#print axioms Contract
#print axioms Comparison
end OwnInit
end PV_LIB_SPEC_Frozen
