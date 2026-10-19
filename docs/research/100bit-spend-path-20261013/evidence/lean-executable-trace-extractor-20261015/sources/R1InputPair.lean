import R1AppendPair
import R1InputPairCopyLinks

/-! The input pair and the occupancy of the slot selected by the literal
trace path. This does not yet strengthen the existential input-note witness
with a complete authenticated pair/forest relation. -/
set_option autoImplicit false
namespace AspisR1.InputPair
open R0P AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K]

attribute [local irreducible] nodeCompress poseidonPermutation

def leaf (A : Trace K) : PairLeaf K where
  firstCommitment := AppendNode.left A 4
  secondOccupied := A 0 1017
  secondCommitment := fun i => A ⟨2 + i.val, by omega⟩ 1017
  secondOccupancyInverse := A 1 1017

theorem leaf_valid (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) : (leaf A).Valid := by
  have h := (occupancy_holds_iff pub A).mp ho |>.1 1017 (Or.inl rfl)
  exact ⟨h.1, sub_eq_zero.mp h.2.1, h.2.2.1, h.2.2.2⟩

theorem pair_output (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    OutputNotes.output A 4 = nodeCompress (leaf A).firstCommitment (leaf A).secondCommitment := by
  rw [AppendNode.node_step pub A hs hpo 4 (nodeBlock_node 0)]
  have hr : AppendNode.right A 4 = (leaf A).secondCommitment := by
    funext i
    exact (InputPairCopyLinks.right_cells pub A hb i).symm
  rw [hr]
  rfl

/-- The path's first side bit selects an occupied slot. The copy link binds
that very bit to the input occupancy gate, rather than assuming spendability. -/
theorem selected_spendable (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) (hb : CopyLinkBalance pub A) :
    (leaf A).SelectedSlotIsSpendable (tracePath A 0).1 := by
  classical
  have hbit := InputPairCopyLinks.selected_bit pub A hb
  have hg := (occupancy_holds_iff pub A).mp ho |>.2.1
  rw [← hbit] at hg
  by_cases hz : A 0 913 = 0
  · have hp : (tracePath A 0).1 = false := by
      simp only [tracePath, pathBaseRow]
      change ((if A 0 913 = 0 then _ else _) : Bool × R0P.Digest K).1 = false
      rw [if_pos hz]
    rw [hp]
    exact first_slot_is_spendable (leaf A)
  · have hp : (tracePath A 0).1 = true := by
      simp only [tracePath, pathBaseRow]
      change ((if A 0 913 = 0 then _ else _) : Bool × R0P.Digest K).1 = true
      rw [if_neg hz]
    rw [hp, second_slot_spendable_iff]
    have hz' : 1 - A 0 1017 = 0 := (mul_eq_zero.mp hg).resolve_left hz
    exact (sub_eq_zero.mp hz').symm

theorem empty_second_rejected (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) (hb : CopyLinkBalance pub A)
    (hempty : (leaf A).secondOccupied = 0) : (tracePath A 0).1 = false := by
  have hs := selected_spendable pub A ho hb
  cases hp : (tracePath A 0).1 with
  | false => rfl
  | true =>
    rw [hp, second_slot_spendable_iff, hempty] at hs
    exact (zero_ne_one hs).elim

#print axioms leaf_valid
#print axioms pair_output
#print axioms selected_spendable
#print axioms empty_second_rejected
end AspisR1.InputPair
