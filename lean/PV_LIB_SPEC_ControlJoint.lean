import PV_LIB_SPEC_JointPremises
import PV_LIB_SPEC_ControlHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ControlJoint
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_ResourceHistory
abbrev NativeFacets := PV_LIB_SPEC_JointPremises.NativeFacets
abbrev nativeFacets := PV_LIB_SPEC_JointPremises.nativeFacets
/-- Current positive-entry/machine/facet/history conjunction. The concrete
store and environment are fixed; ABI DATA and the completed lane-A table
remain explicit. This does not certify the frozen binary ABI, an allocation
history, or any row contract. -/
def EntryMachinePremises (table : FullStoreActionTable) (p : Parameters)
    (abi : ABI) (i : OwnInit.Input) (m : PV_LIB_SPEC_ControlRuntime.Machine) : Prop :=
  OwnInit.Pre p i ∧ 0 < i.n ∧
  PV_LIB_SPEC_ControlRuntime.MachineSpec table p abi m ∧ NativeFacets p ∧
  (∀ n, PV_LIB_SPEC_ControlHistory.Invariant
    (PV_LIB_SPEC_ControlRuntime.run table p abi n (initial i))) ∧
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
      (PV_LIB_SPEC_ControlRuntime.source table PV_LIB_SPEC_ConcreteEntry.parameters abi) := by
  refine ⟨PV_LIB_SPEC_ConcreteEntry.pre,by decide,rfl,nativeFacets,?_,?_,?_⟩
  · intro n
    exact PV_LIB_SPEC_ControlHistory.original table _ abi _ n
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
        (PV_LIB_SPEC_ControlRuntime.source table PV_LIB_SPEC_ConcreteEntry.parameters abi) :=
  ⟨inventory,entryMachine table abi⟩

#print axioms NativeFacets
#print axioms nativeFacets
#print axioms EntryMachinePremises
#print axioms entryMachine
#print axioms TableRequirement
#print axioms withTable
end PV_LIB_SPEC_ControlJoint
