import PV_B3P_Output133
import PV_B3P_ReferenceValue133
import PV_B3P_StructuralLemmas133
import PV_B3P_Adjacent133
namespace PV_B3P_Closure133
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

-- Algorithm-independent value transport: all ascending sorted permutations
-- give the same result after adjacent deduplication.
theorem sorted_value (rows : List Nat) (hs : rows.Pairwise (· ≤ ·))
    (hp : rows.Perm PV_B3P_Sorted133.input) :
    PV_B3P_Adjacent133.adjacent rows = PV_B3P_Sorted133.expected := by
  apply PV_B3P_Adjacent133.value _ _ hs PV_B3P_Ordered133.expected_ordered
  intro z
  exact hp.mem_iff.trans ⟨fun h => PV_B3P_InputMembers133.subset h,
                         fun h => PV_B3P_OutputMembers133.subset h⟩

theorem value_nat : PV_B3P_Install133.value.val.map (fun x => x.val) =
    PV_B3P_Sorted133.expected := PV_B3P_ReferenceValue133.reference_values

theorem row_law (base : ExternalTypes) (ops : @ExternalFuns base) :
    ∃ rows : alloc.vec.Vec U16,
      @ExternalFuns.op133 base (PV_B3P_Install133.selected base ops) = .ok (.Ok rows) ∧
      rows.val.map (fun x => x.val) = PV_B3P_Sorted133.expected ∧
      rows.val.length = 214 ∧
      PV_B3P_SortedResult133.active = .ok (rows.val.map (fun x => x.val)) := by
  refine ⟨PV_B3P_Install133.value,PV_B3P_Install133.source base ops,value_nat,
    PV_B3P_Output133.value_length,?_⟩
  rw [value_nat]
  exact PV_B3P_SortedResult133.complete_result

-- This is the complete selected-callback law. The external structural receipt
-- binds its owned reference to native Rust; no native machine equality axiom
-- or Kani premise is introduced here. All other callback frames are in Install133.
#print axioms sorted_value
#print axioms value_nat
#print axioms row_law
end
end PV_B3P_Closure133
