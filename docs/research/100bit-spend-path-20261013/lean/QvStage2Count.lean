import QvStage1Count

/-! Binary batch B counting. Source/profile and effect-log transport remain
explicit premises; no universe of 2^18 leaves is evaluated. -/
set_option autoImplicit false
namespace AspisR1.QvStage2
open QvStage1

def resumeBudget : Nat := 3

def stage2Budget (k : Nat) : Nat := resumeBudget + 3 * k + batchParents k

theorem stage2Budget_closed (k : Nat) : stage2Budget k = 43 * k + 50 := by
  simp only [stage2Budget, resumeBudget, batchParents, fullParents, foldedParents]
  omega

theorem stage2Budget_twelve : stage2Budget 12 = 566 := by
  rw [stage2Budget_closed]

theorem batchB_parents : batchParents 12 = 527 := rfl

/-- Supplied nodes are bytes, not additional oracle positions. This is the
exact binary-trie telescoping relation, with all three root hashes included. -/
theorem batch_reads_balance (a b c : Trie) :
    (a.leaves + b.leaves + c.leaves + a.parents + b.parents + c.parents) + 3 =
      (a.supplied + b.supplied + c.supplied) +
        2 * (a.leaves + b.leaves + c.leaves) := by
  have := a.balance
  have := b.balance
  have := c.balance
  omega

/-- Batch B uses slots 3..5 of the 914-node format, capped at 172+172+150.
This uses a B-specific cap, not the invalid subtraction of A's maximum
from a global bound on actual consumption. -/
theorem batchB_reads_of_slots (a b c : Trie)
    (hs : a.supplied + b.supplied + c.supplied ≤ 494)
    (hl : a.leaves + b.leaves + c.leaves ≤ 36) :
    a.leaves + b.leaves + c.leaves + a.parents + b.parents + c.parents ≤ 563 := by
  have := batch_reads_balance a b c
  omega

/-- Exact counts at the maximal twelve-distinct-leaf profiles. -/
theorem batchB_extreme_counts (a b c : Trie)
    (ha : a.parents = fullParents 12) (hb : b.parents = fullParents 12)
    (hc : c.parents = foldedParents 12)
    (hla : a.leaves = 12) (hlb : b.leaves = 12) (hlc : c.leaves = 12) :
    a.supplied = 172 ∧ b.supplied = 172 ∧ c.supplied = 150 ∧
    a.parents + b.parents + c.parents = 527 ∧
    a.leaves + b.leaves + c.leaves + a.parents + b.parents + c.parents = 563 := by
  have := a.balance
  have := b.balance
  have := c.balance
  simp only [fullParents, foldedParents] at *
  omega

/-- Completeness is required for every rejection/suspension prefix, including
repeated leaf calls before folded-key deduplication. `finish_relation` has
no designated Digest32 calls; effectful observers need their own coverage. -/
structure CountedTrace {Call : Type} (k : Nat) (tr : List Call) : Prop where
  pieces : ∃ resume leaves parents : List Call,
    tr.Perm (resume ++ leaves ++ parents) ∧
    resume.length ≤ resumeBudget ∧ leaves.length ≤ 3 * k ∧
    parents.length ≤ batchParents k

theorem countedTrace_bound {Call : Type} {k : Nat} {tr : List Call}
    (h : CountedTrace k tr) : tr.length ≤ stage2Budget k := by
  obtain ⟨rs, ls, ps, hp, hr, hl, hn⟩ := h.pieces
  have he := hp.length_eq
  simp only [List.length_append] at he
  unfold stage2Budget
  omega

/-- The sum is conservative even when both transactions repeat an address. -/
def verifierBudget : Nat := QvStage1.stage1Budget 10 + stage2Budget 12

theorem verifierBudget_value : verifierBudget = 1161 := by
  rw [verifierBudget, QvStage1.stage1Budget_ten, stage2Budget_twelve]

#print axioms stage2Budget_closed
#print axioms stage2Budget_twelve
#print axioms batchB_parents
#print axioms batch_reads_balance
#print axioms batchB_reads_of_slots
#print axioms batchB_extreme_counts
#print axioms countedTrace_bound
#print axioms verifierBudget_value
end AspisR1.QvStage2
