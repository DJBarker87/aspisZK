import PV_LIB_SPEC_OwnInitCut92Contract
import PV_LIB_SPEC_OwnInitComposition
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Cut92Composition
open PV_STX_Machine PV_STX2_Syntax PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
abbrev Implementations := PV_LIB_SPEC_OwnInitComposition.Implementations
/-- SPEC-C5-only replacement in the full conjunction. All other seventeen
contracts and the historical source/runtime parameters are unchanged. This
is a TARGET, not a claim that the sparse/v2 runtime meets these contracts. -/
def OwnContract (table : FullStoreActionTable) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementation : Machine → OwnInit.Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → OwnInit.Pre p i →
    PV_LIB_SPEC_OwnInitCut92Contract.Post table (runtime p)
      (OwnInit.representation p granted) i (implementation m i)

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
  OwnContract table p granted implementations.ownInit

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
      PV_LIB_SPEC_OwnInitCut92.AllocationWitness table (runtime p)
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

#print axioms Implementations
#print axioms OwnContract
#print axioms Contracts
#print axioms AllocationBranch
#print axioms Witness
end PV_LIB_SPEC_Cut92Composition
