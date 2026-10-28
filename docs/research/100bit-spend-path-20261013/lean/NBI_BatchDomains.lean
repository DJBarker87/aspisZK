import NBE_BatchDomains
import NBI_CountScan
import Port4B_LeafStep

set_option autoImplicit false
namespace AspisR1.NBI_BatchDomains
open Aeneas Aeneas.Std Result

/-- The post-hash dedup step's index and predecessor domains hold at every
active key position, for either split, even when a duplicate later rejects. -/
theorem reached_dedup (batch : Usize) (position distinct : Nat)
    (active : position < (Port4B_TreeCuts.count batch).val)
    (invariant : distinct ≤ position) :
    distinct < 12 ∧ distinct+1 ≤ position+1 ∧
    (0 < distinct → distinct-1 < 16) ∧
    position+1 ≤ (Port4B_TreeCuts.count batch).val := by
  have bound := NBE_BatchDomains.key_domain batch position active
  have counts := Port4B_Bounds.count batch
  by_cases zero : batch = 0#usize
  · rw [if_pos zero] at counts
    omega
  · rw [if_neg zero] at counts
    omega

/-- Eight-byte padding iterations cover the SAME suffix selected by the
count, without an unexamined partial word or an assumed zero-padding law. -/
theorem padding_domain (capacity count word : Nat) (cap : capacity ≤ 172)
    (counted : count ≤ capacity) (active : word < 4*(capacity-count)) :
    32*count+8*word+8 ≤ 32*capacity ∧ 32*capacity ≤ 5504 ∧
    (32*capacity-32*count)%8 = 0 := by omega

/-- A native new-key step preserves the needed distinct-count bound; a
native duplicate keeps the count. This is independent of leaf equality. -/
theorem next_distinct (position distinct : Nat) (safe : distinct ≤ position)
    (duplicate : Bool) :
    (if duplicate then distinct else distinct+1) ≤ position+1 := by
  cases duplicate <;> simp_all <;> omega

#print axioms reached_dedup
#print axioms padding_domain
#print axioms next_distinct
end AspisR1.NBI_BatchDomains
