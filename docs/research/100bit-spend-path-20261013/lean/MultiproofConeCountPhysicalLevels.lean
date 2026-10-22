import MultiproofConeCountPhysical
import MultiproofConeCountBounds

set_option autoImplicit false
namespace AspisR1.MultiproofConeCountPhysicalLevels
open OraclePortFrozenOrder MultiproofConeCountPhysical MultiproofConeCountLevels
open MultiproofConeLiveOrder

theorem rebuild (xs : List Nat) : cells (fun j => xs[j]!) 0 xs.length=xs := by
  apply List.ext_getElem
  · simp only [cells,List.length_map,List.length_range]
  · intro j hj hj'
    simp only [cells,List.getElem_map,List.getElem_range,Nat.zero_add]
    exact getElem!_pos xs j hj'

/-- A level's scratch suffix is observationally irrelevant after n=w. The
next live view can be represented by any array with exactly this prefix. -/
def physicalCount : Nat → (Nat → Nat) → Nat → Nat
  | 0,_,_ => 0
  | height+1,k,n => let out := rows n k n 0 0 0
                    out.2+physicalCount height (fun j => out.1[j]!) out.1.length

theorem physical_count_eq (height : Nat) (k : Nat → Nat) (n : Nat) :
    physicalCount height k n=nodeCount height (cells k 0 n) := by
  induction height generalizing k n with
  | zero => rfl
  | succ height ih =>
    simp only [physicalCount,level_projection,ih,rebuild,nodeCount]
    have length : (cells k 0 n).length=n := by simp [cells]
    rw [length]

/-- The replacement Kani gate's unread-order/range domain is invariant
under the exact in-place index write and advancing cursor. -/
theorem unread_domain (k : Nat → Nat) (n i w : Nat) (safe : w ≤ i) (active : i<n)
    (order : (unread k n i).Pairwise (·<·))
    (range : ∀ j∈unread k n i, j<262144) :
    (unread (write k i w) n (advance k n i)).Pairwise (·<·) ∧
      ∀ j∈unread (write k i w) n (advance k n i), j<262144 := by
  have advance := advance_bounds k n i active
  rw [unread_write k n i w _ (by omega),←(group_tail k n i active).2]
  rw [unread_cons k n i active] at order range
  have tailOrder := (List.pairwise_cons.mp order).2
  have tailRange : ∀ j∈unread k n (i+1), j<262144 :=
    fun j mem => range j (List.mem_cons_of_mem _ mem)
  split
  · exact ⟨tailOrder.drop,fun j mem => tailRange j (List.mem_of_mem_drop mem)⟩
  · exact ⟨tailOrder,tailRange⟩

theorem next_domain (is : List Nat) (order : is.Pairwise (·<·))
    (size : is.length≤16) (range : ∀ j∈is, j<262144) :
    ((countLevel is.length is).1).Pairwise (·<·) ∧
      (countLevel is.length is).1.length≤16 ∧
      ∀ j∈(countLevel is.length is).1, j<262144 := by
  refine ⟨sorted _ _ order,?_,?_⟩
  · have bound := MultiproofConeCountBounds.level_bounds is.length is;omega
  · intro j mem
    obtain ⟨i,hi,rfl⟩ := members is.length is j mem
    have upper := range i hi
    have div := Nat.div_le_self i 2
    omega

/-- Full physical count projection equals the source equal-parent recurrence
and frozen nodeCount, with the local gate domain proved along every level. -/
theorem eighteen_count (k : Nat → Nat) (n : Nat)
    (order : (cells k 0 n).Pairwise (·<·)) :
    physicalCount 18 k n=sourceCount 18 (cells k 0 n) := by
  rw [physical_count_eq,count_eq _ _ order]

#print axioms rebuild
#print axioms physical_count_eq
#print axioms unread_domain
#print axioms next_domain
#print axioms eighteen_count
end AspisR1.MultiproofConeCountPhysicalLevels
