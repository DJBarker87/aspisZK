import PV_LIB_SPEC_F316Callback
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_OwnInitComposition
open PV_STX_Machine PV_STX2_Syntax PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
/-- Independent candidate executions. These are data functions; none of their
contract proofs is hidden in a machine or an entry precondition. -/
structure Implementations where
  f361 : Machine → F361.Input → Nat → State
  f316 : Machine → PV_LIB_SPEC_F316Callback.Input → Nat → State
  f0 : Machine → F0.Input → Nat → State
  ownInit : Machine → OwnInit.Input → Nat → State
  f270 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f166 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f15 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f208 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f220 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f318 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f219 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f125 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f6 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f170 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f17 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f5 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f2 : Machine → PV_LIB_SPEC_Row.Input → Nat → State
  f1 : Machine → PV_LIB_SPEC_Row.Input → Nat → State

/-- The eighteen whole statements share ONE completed writer table, runtime,
source symbols, resources and environment. f316 includes intrinsic callbacks
with no ordinary caller. This is a proposition, not a proof of composition. -/
def Contracts (table : FullStoreActionTable) (p : Parameters)
    (R : F361.Representation) (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementations : Implementations) : Prop :=
  F361.Contract table p R implementations.f361 ∧
  F270.Contract table p implementations.f270 ∧
  F166.Contract table p implementations.f166 ∧
  F15.Contract table p implementations.f15 ∧
  F208.Contract table p implementations.f208 ∧
  F220.Contract table p implementations.f220 ∧
  PV_LIB_SPEC_F316Callback.Contract table p implementations.f316 ∧
  F318.Contract table p implementations.f318 ∧
  F219.Contract table p implementations.f219 ∧
  F125.Contract table p implementations.f125 ∧
  F6.Contract table p implementations.f6 ∧
  F170.Contract table p implementations.f170 ∧
  F17.Contract table p implementations.f17 ∧
  F5.Contract table p implementations.f5 ∧
  F2.Contract table p implementations.f2 ∧
  F1.Contract table p implementations.f1 ∧
  F0.Contract table p implementations.f0 ∧
  OwnInit.Contract table p granted implementations.ownInit

/-- A NONEMPTY continuous original-entry allocation branch, not an implication
whose antecedent postulates reaching the desired cut. The actual source run
contains the callback allocation, registration, tagged payload, bridged decode
and ThreadInit allocation/ownership witness in this order. No success premise
is added to ANY row: failure/no-box/pending/abort branches stay in Contracts. -/
def AllocationBranch (table : FullStoreActionTable) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) : Prop :=
  ∃ i : OwnInit.Input, OwnInit.Pre p i ∧ 0 < i.n ∧
    ∃ before : Nat,
      let trace := fun k => run (source table p) k (PV_LIB_SPEC_F0Full.rootEntry i)
      PV_LIB_SPEC_OwnInitFull.InitPoll (trace before) ∧
      PV_LIB_SPEC_OwnInitFull.AllocationWitness table (runtime p)
        (OwnInit.representation p granted) i trace (before+1)

/-- Joint nonemptiness target, with all eighteen universal contracts and one
actual original-entry allocation history in the SAME model. `sourceWrites`
is lane A's independent full D984 inventory (including allocated source cells),
not a list inferred from whichever table happens to be supplied. This remains
an UNPROVED statement; an entry-only Unit model is not its inhabitant. -/
def Witness (sourceWrites : Data → Prop) : Prop :=
  ∃ (table : FullStoreActionTable) (p : Parameters) (R : F361.Representation)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions) (implementations : Implementations),
    TableAdequacy table sourceWrites ∧
    Contracts table p R granted implementations ∧ AllocationBranch table p granted

/-- Exact existing exports to be applied at the allocation history above.
Their availability alone does not discharge Witness. -/
abbrev AllocationExport := @PV_THR2_OwnInitActualAllocationOwned.allBridged
abbrev OwnershipExport := @PV_OWN2_Exports.SourceInitBoxOwnership
#print axioms Implementations
#print axioms Contracts
#print axioms AllocationBranch
#print axioms Witness
#print axioms AllocationExport
#print axioms OwnershipExport
end PV_LIB_SPEC_OwnInitComposition
