import Port4B_LeafStep
import BEl_NativeBatchCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_GateBounds
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- The only two continuing counter updates in the literal reference body. -/
inductive Counters : Nat → Nat → Prop where
  | initial : Counters 0 0
  | duplicate {d p : Nat} (prior : Counters d p) : Counters d (p+1)
  | distinct {d p : Nat} (prior : Counters d p) : Counters (d+1) (p+1)

theorem used_le_position {d p : Nat} (history : Counters d p) : d ≤ p := by
  induction history <;> omega

theorem leaf_domain {d p n : Nat} (history : Counters d p) (size : n=10 ∨ n=12) (active : p<n) :
    d≤p ∧ p<12 ∧ d<16 := by
  have bounded := used_le_position history
  rcases size with rfl|rfl <;> omega

/-- Existing P6 insertion, including duplicate failure, grows used by at most1.
This reuses its exact native/reference post-step theorem rather than replaying
an array or scratch induction. -/
theorem insertion_growth (s t : reference.Scratch) (index : U32)
    (leaf : MultiproofConePhysicalLive.Digest) (room : s.n.val<16)
    (step : MultiproofConeLeafContent.next s index leaf room = some t) :
    t.n.val ≤ s.n.val+1 := by
  unfold MultiproofConeLeafContent.next at step
  split at step
  · split at step
    · have same := Option.some.inj step
      subst t
      omega
    · cases step
  · have same := Option.some.inj step
    subst t
    scalar_tac

theorem packed_position (index position : Nat) (small : position<256) :
    (index*256+position)%256=position := by
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_add,
    Nat.mod_eq_of_lt small]

theorem opening_domain (batch : Fin 2) (position : Nat)
    (active : position < if batch.val=0 then 10 else 12) :
    (if batch.val=0 then 0 else 10)+position<22 := by
  split at active ⊢ <;> omega

theorem opening_extent (selected : Nat) (bounded : selected<22) :
    10055+selected*832+832 ≤ 28359 ∧ 28359 ≤ 57607 := by omega

theorem padding_domain (count capacity : Nat) (guard : count≤capacity) (cap : capacity≤172) :
    32*count≤32*capacity ∧ 32*capacity≤5504 ∧
    (32*capacity-32*count)%8=0 := by
  have split : 32*capacity-32*count = 32*(capacity-count) := Nat.mul_sub_left_distrib _ _ _
  refine ⟨by omega,by omega,?_⟩
  rw [split,Nat.mul_mod]
  rfl

#print axioms used_le_position
#print axioms leaf_domain
#print axioms insertion_growth
#print axioms packed_position
#print axioms opening_domain
#print axioms opening_extent
#print axioms padding_domain
end AspisR1.BEl_GateBounds
end
