import RPu_FJc_SubsetModel
import RPt_FJc_ReadSlot
set_option autoImplicit false
namespace AspisR1.FJc_GroupTable
open Aeneas Aeneas.Std Result

def group (j : Nat) : Nat :=
  match FIo_Native.weights.S2_INACTIVE_GROUPS.val[j]? with | some g => g.val | none => 0

theorem entries : ∀ g∈FIo_Native.weights.S2_INACTIVE_GROUPS.val,g.val<12 := by
  simp [FIo_Native.weights.S2_INACTIVE_GROUPS,Array.make]

theorem bound (j : Nat) (hj : j<64) : group j<12 := by
  have hi : j<FIo_Native.weights.S2_INACTIVE_GROUPS.val.length := by
    rw [FIo_Native.weights.S2_INACTIVE_GROUPS.property];exact hj
  unfold group
  rw [List.getElem?_eq_getElem hi]
  exact entries _ (List.getElem_mem hi)
#print axioms entries
#print axioms bound
end AspisR1.FJc_GroupTable
