import NBJ_CountRows

set_option autoImplicit false
namespace AspisR1.NBJ_CountLevels
open MultiproofConeCountPhysical MultiproofConeCountPhysicalLevels MultiproofConeLiveOrder

/-- Preserve the native count's equal-parent scan at every level. -/
def nativeCount : Nat → (Nat → Nat) → Nat → Nat
  | 0,_,_ => 0
  | h+1,key,n =>
      let out := NBJ_CountRows.nativeRows n key n 0 0 0
      out.2 + nativeCount h (fun j => out.1[j]!) out.1.length

theorem strict_cells (key : Nat → Nat) (n : Nat)
    (order : (cells key 0 n).Pairwise (·<·)) : Strict key 0 n := by
  intro a b lo asc hi
  have len : (cells key 0 n).length = n := by simp [cells]
  have eq := List.pairwise_iff_getElem.mp order a b (by omega) (by omega) asc
  simpa only [cells,List.getElem_map,List.getElem_range,Nat.zero_add] using eq

/-- Both the inner rows and the next level's order are derived from the same
source prestate. No assumed per-level result or supplied final count occurs. -/
theorem count_port (height : Nat) (key : Nat → Nat) (n : Nat)
    (order : (cells key 0 n).Pairwise (·<·)) :
    nativeCount height key n = physicalCount height key n := by
  induction height generalizing key n with
  | zero => rfl
  | succ height ih =>
    have row := NBJ_CountRows.rows_port n key n 0 0 0 (by omega) (by omega)
      (strict_cells key n order)
    simp only [nativeCount,physicalCount,row]
    congr 1
    apply ih
    rw [rebuild,level_projection]
    exact MultiproofConeCountLevels.sorted n (cells key 0 n) order

/-- Source eighteen-level control consumes the inherited complete count
projection; the source scan recurrence is retained, rather than assumed. -/
theorem eighteen (key : Nat → Nat) (n : Nat)
    (order : (cells key 0 n).Pairwise (·<·)) :
    nativeCount 18 key n = MultiproofConeCountLevels.sourceCount 18 (cells key 0 n) := by
  rw [count_port 18 key n order]
  exact eighteen_count key n order

#print axioms strict_cells
#print axioms count_port
#print axioms eighteen
end AspisR1.NBJ_CountLevels
