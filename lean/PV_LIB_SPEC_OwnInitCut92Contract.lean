import PV_LIB_SPEC_OwnInitCut92
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_OwnInitCut92Contract
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_OwnInitFull.Input
abbrev Representation := PV_LIB_SPEC_OwnInitFull.Representation
abbrev entry := PV_LIB_SPEC_OwnInitFull.entry
/-- Approved SPEC-C5 propagated through the complete own-row Post and Contract.
Only the witness name changes. This does NOT assert source adequacy of the
historical Runtime, nor rebind it to the new sparse/v2 execution. -/
def Post (table : FullStoreActionTable) (r : Runtime) (R : Representation)
    (i : Input) (candidate : Nat → State) : Prop :=
  let m := PV_LIB_SPEC_Full.source table r
  let ref := fun n => run m n (entry i)
  ((∃ n k, PV_LIB_SPEC_OwnInitFull.First m i ref n ∧ PV_LIB_SPEC_OwnInitFull.First m i candidate k ∧
      PV_LIB_SPEC_Frontier.observe (candidate k) = PV_LIB_SPEC_Frontier.observe (ref n) ∧
      ((∃ before, n = before+1 ∧ PV_LIB_SPEC_OwnInitFull.InitPoll (ref before)) →
        PV_LIB_SPEC_OwnInitCut92.AllocationWitness table r R i ref n)) ∨
    ((∀ n, ¬ PV_LIB_SPEC_OwnInitFull.Boundary m i ref n) ∧ (∀ k, ¬ PV_LIB_SPEC_OwnInitFull.Boundary m i candidate k) ∧
      (∀ n, ∃ k, (ref n).current.events = (candidate k).current.events) ∧
      (∀ k, ∃ n, (ref n).current.events = (candidate k).current.events))) ∧
  ∀ k, (∀ j, j < k → ¬ PV_LIB_SPEC_OwnInitFull.Boundary m i candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) →
      PV_LIB_SPEC_F0Full.RootFrame r i (candidate k)

def Contract (table : FullStoreActionTable) (r : Runtime) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, PV_LIB_SPEC_Full.MachineSpec table r m → PV_LIB_SPEC_OwnInitFull.Pre r i → Post table r R i (implementation m i)
#print axioms Input
#print axioms Representation
#print axioms entry
#print axioms Post
#print axioms Contract
end PV_LIB_SPEC_OwnInitCut92Contract
