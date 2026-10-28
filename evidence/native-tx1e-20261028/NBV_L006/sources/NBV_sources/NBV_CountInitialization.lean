import NBJ_CountLevels
import KMX_CopyMeaning

set_option autoImplicit false
namespace AspisR1.NBV_CountInitialization
open MultiproofConeCountPhysical MultiproofConeLiveOrder

def initialized (key : Nat → Nat) (n : Nat) : Nat → Nat :=
  KMX_CopyMeaning.loop key (fun _ => 0) 0 n

/-- The count prestate is constructed by the mitigated prefix-copy value law,
including an exact zero suffix. No final native array equation is assumed. -/
theorem initialized_cell (key : Nat → Nat) (n k : Nat) :
    initialized key n k = if k < n then key k else 0 := by
  exact KMX_CopyMeaning.copy_prefix key (fun _ => 0) n k

theorem initialized_live (key : Nat → Nat) (n : Nat) :
    cells (initialized key n) 0 n = cells key 0 n := by
  apply List.ext_getElem
  · simp only [cells,List.length_map,List.length_range]
  · intro k ha hb
    have bound : k < n := by simpa only [cells,List.length_map,List.length_range] using ha
    simp only [cells,List.getElem_map,List.getElem_range,Nat.zero_add]
    exact (initialized_cell key n k).trans (if_pos bound)

/-- Construct the SAME count initial carrier before consuming the existing
source scan/height induction. This is a model/value theorem, not an assumed
nativeCount result or an enclosing native verification claim. -/
theorem count_initialized (key : Nat → Nat) (n : Nat)
    (ordered : (cells key 0 n).Pairwise (·<·)) :
    NBJ_CountLevels.nativeCount 18 (initialized key n) n =
      MultiproofConeCountLevels.sourceCount 18 (cells key 0 n) := by
  have live := initialized_live key n
  have order : (cells (initialized key n) 0 n).Pairwise (·<·) := by
    rw [live]
    exact ordered
  rw [NBJ_CountLevels.eighteen (initialized key n) n order,live]

#print axioms initialized_cell
#print axioms initialized_live
#print axioms count_initialized
end AspisR1.NBV_CountInitialization
