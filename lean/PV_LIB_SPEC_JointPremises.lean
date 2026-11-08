import PV_LIB_SPEC_ConcreteEntry
import PV_LIB_SPEC_HistoryInvariant
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_JointPremises
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_ResourceHistory

/-- Exact named native facets present in the imported OwnInit/TLS contracts.
No Store transformer, target output store or decoder success is a field.
Atomic's finalStore argument is the empty input delta of its PURE value
constructor, not a source-store write assumption for Arc or other writers. -/
structure NativeFacets (p : Parameters) : Prop where
  atomic : ∀ (e : PV_W1_LeafBoundary.Entry) (w : OWNER) (n : Nat),
    PV_THR2_LibrarySemantics_AtomicUsizeNew.Fact (runtime p).carrier e
      p.environment.native w (fun _ => none) n
  tlsSource : PV_FN_THREAD_f170.DocumentedSourceFacts (runtime p).carrier p.environment.native
  tlsWorld : PV_FN_THREAD_f170.DocumentedValueFacts p.environment.native
  backendGhost : ∀ request w,
    GhostFrame w (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w).world

/-- ONE concrete pending external/resource environment jointly satisfies the
named all-answer world facets and all conditional returned-value facets.
This is logical nonemptiness, not a claim that a pure Rust function suspends
in the frozen binary or that any successful OwnInit allocation was reached. -/
theorem nativeFacets : NativeFacets PV_LIB_SPEC_ConcreteEntry.parameters := by
  constructor
  · intro e w n result returned
    cases returned
  · constructor
    · intro e w v; dsimp only; intro returned; cases returned
    · intro e w v; dsimp only; intro returned; cases returned
    · intro e w v; dsimp only; intro returned; cases returned
  · exact ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  · exact backend_framed PV_LIB_SPEC_ConcreteEntry.parameters

/-- The OLD full-row realization target includes universal row correctness
and a successful allocation history. It is intentionally retained unchanged.
This new conjunction records only the concrete entry, machine, named facets
and resource-history association actually inhabited here. ABI SOURCE/BINARY
association is NOT silently replaced by an arbitrary witness of ABI's type. -/
def EntryMachinePremises (table : FullStoreActionTable) (p : Parameters)
    (abi : ABI) (i : OwnInit.Input) (m : PV_LIB_SPEC_BoundRuntime.Machine) : Prop :=
  OwnInit.Pre p i ∧ 0 < i.n ∧
  PV_LIB_SPEC_BoundRuntime.MachineSpec table p abi m ∧ NativeFacets p ∧
  (∀ n, PV_LIB_SPEC_HistoryInvariant.Invariant
    (PV_LIB_SPEC_BoundRuntime.run table p abi n (initial i))) ∧
  (∀ ctx {A : Type} (op : PV_EVHB_GlobalSystem.Primitive A) before,
    allocationResources p.environment ctx op before =
      p.environment.allocation ⟨ctx.site,ctx.occurrence,ctx.arguments,op,before⟩) ∧
  (∀ ctx {A : Type} (op : PV_EVHB_GlobalSystem.Primitive A) before,
    reservationResources p.environment ctx op before =
      p.environment.reservation ⟨ctx.site,ctx.occurrence,ctx.arguments,op,before⟩)

/-- A concrete state/environment/machine recipe, parametric in ABI DATA and
lane A's table. No row is proved. The table is not required to produce a
desired store; source coverage and exact documented meanings are separately
lane A's adequacy obligation. This is NOT a full source-adequate joint witness:
the native pending environment does not witness AllocationBranch, and the
actual frozen ABI still must replace this explicit data parameter. -/
theorem entryMachine (table : FullStoreActionTable) (abi : ABI) :
    EntryMachinePremises table PV_LIB_SPEC_ConcreteEntry.parameters abi
      PV_LIB_SPEC_ConcreteEntry.input
      (PV_LIB_SPEC_BoundRuntime.source table PV_LIB_SPEC_ConcreteEntry.parameters abi) := by
  refine ⟨PV_LIB_SPEC_ConcreteEntry.pre,by decide,rfl,nativeFacets,?_,?_,?_⟩
  · intro n
    exact PV_LIB_SPEC_HistoryInvariant.original table _ abi _ n
  · exact allocation_binding _
  · exact reservation_binding _

/-- The explicit full-table requirement carries only inventory uniqueness,
coverage and source labels. Exact meanings are supplied by lane A's named
interpretations, not an assumption of definedness at a future source call. -/
def TableRequirement (sourceWrites : Data → Prop) (table : FullStoreActionTable) : Prop :=
  TableAdequacy table sourceWrites

theorem withTable (sourceWrites : Data → Prop) (table : FullStoreActionTable)
    (abi : ABI) (inventory : TableRequirement sourceWrites table) :
    TableRequirement sourceWrites table ∧
      EntryMachinePremises table PV_LIB_SPEC_ConcreteEntry.parameters abi
        PV_LIB_SPEC_ConcreteEntry.input
        (PV_LIB_SPEC_BoundRuntime.source table PV_LIB_SPEC_ConcreteEntry.parameters abi) :=
  ⟨inventory,entryMachine table abi⟩

#print axioms NativeFacets
#print axioms nativeFacets
#print axioms EntryMachinePremises
#print axioms entryMachine
#print axioms TableRequirement
#print axioms withTable
end PV_LIB_SPEC_JointPremises
