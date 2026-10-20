import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-! Symbolic binary multiproof counting. No leaf-universe enumeration.
The profile premise is intentionally separate from source refinement. -/
set_option autoImplicit false
namespace AspisR1.QvStage1

/-- An occupied binary trie. `unary` consumes one supplied sibling digest;
`fork` combines two occupied subtries. The top parent is included. -/
inductive Trie where
  | leaf
  | unary (child : Trie)
  | fork (left right : Trie)

def Trie.leaves : Trie → Nat
  | .leaf => 1
  | .unary t => t.leaves
  | .fork l r => l.leaves + r.leaves

def Trie.supplied : Trie → Nat
  | .leaf => 0
  | .unary t => t.supplied + 1
  | .fork l r => l.supplied + r.supplied

def Trie.parents : Trie → Nat
  | .leaf => 0
  | .unary t => t.parents + 1
  | .fork l r => l.parents + r.parents + 1

/-- Exact telescoping identity, including the root hash. -/
theorem Trie.balance (t : Trie) : t.parents + 1 = t.supplied + t.leaves := by
  induction t <;> simp_all [Trie.parents, Trie.supplied, Trie.leaves] <;> omega

/-- Plateau plus a small crown. `full`: levels 1..14 bounded by k,
then 8,4,2,1. `folded`: levels 1..12 bounded by k, then 8,4,2,1,1,1.
This records the occupied range of the padded folded tree. -/
def fullParents (k : Nat) : Nat := 14 * k + (8 + 4 + 2 + 1)
def foldedParents (k : Nat) : Nat := 12 * k + (8 + 4 + 2 + 1 + 1 + 1)
def batchParents (k : Nat) : Nat := 2 * fullParents k + foldedParents k

theorem plateau_sum_le (xs : List Nat) (k : Nat) (h : ∀ x ∈ xs, x ≤ k) :
    xs.sum ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Counting a level profile only requires its short plateau and crown caps. -/
theorem profile_bound (low crown : List Nat) (k levels cap : Nat)
    (hl : low.length = levels) (hb : ∀ x ∈ low, x ≤ k)
    (hc : crown.sum ≤ cap) : (low ++ crown).sum ≤ levels * k + cap := by
  have h := plateau_sum_le low k hb
  rw [List.sum_append, hl] at *
  omega

/-- The profile equations are the precise remaining range/cardinality bridge.
No claim is made that an arbitrary list is a verifier profile. -/
theorem batch_profile_bound (a b c ac bc cc : List Nat) (k : Nat)
    (ha : a.length = 14) (hb : b.length = 14) (hc : c.length = 12)
    (hba : ∀ x ∈ a, x ≤ k) (hbb : ∀ x ∈ b, x ≤ k)
    (hbc : ∀ x ∈ c, x ≤ k)
    (hca : ac.sum ≤ 15) (hcb : bc.sum ≤ 15) (hcc : cc.sum ≤ 17) :
    (a ++ ac).sum + (b ++ bc).sum + (c ++ cc).sum ≤ batchParents k := by
  have := profile_bound a ac k 14 15 ha hba hca
  have := profile_bound b bc k 14 15 hb hbb hcb
  have := profile_bound c cc k 12 17 hc hbc hcc
  simp only [batchParents, fullParents, foldedParents]
  omega

def transcriptBudget : Nat := 1 + 27 * 3 + 1 + 4 * 3 + 17 + 3
/-- Whole-proof, verbatim ASF8, and checkpoint checksum reads. -/
def checkpointBudget : Nat := 3
/-- Closed-form bound on calls, hence also on distinct first reads. -/
def stage1Budget (k : Nat) : Nat :=
  transcriptBudget + 3 * k + batchParents k + checkpointBudget

theorem stage1Budget_closed (k : Nat) : stage1Budget k = 43 * k + 165 := by
  simp only [stage1Budget, transcriptBudget, batchParents, fullParents,
    foldedParents, checkpointBudget]
  omega

theorem stage1Budget_ten : stage1Budget 10 = 595 := by
  rw [stage1Budget_closed]

theorem batchA_parents : batchParents 10 = 447 := rfl

theorem batchA_supplied (a b c : Trie)
    (ha : a.parents ≤ fullParents 10) (hb : b.parents ≤ fullParents 10)
    (hc : c.parents ≤ foldedParents 10)
    (hla : a.leaves = 10) (hlb : b.leaves = 10) (hlc : c.leaves = 10) :
    a.supplied + b.supplied + c.supplied ≤ 420 := by
  have := a.balance
  have := b.balance
  have := c.balance
  simp only [fullParents, foldedParents] at *
  omega

/-- Explicit extraction obligations: lengths concern ALL calls, including
repeats and failure prefixes. The bound is not inferred from acceptance.
Accounting may permute calls because each tree interleaves leaves/parents;
the original execution trace itself is never reordered. -/
structure CountedTrace {Call : Type} (k : Nat) (tr : List Call) : Prop where
  pieces : ∃ transcript leaves parents checkpoint : List Call,
    tr.Perm (transcript ++ leaves ++ parents ++ checkpoint) ∧
    transcript.length ≤ transcriptBudget ∧ leaves.length ≤ 3 * k ∧
    parents.length ≤ batchParents k ∧ checkpoint.length ≤ checkpointBudget

theorem countedTrace_bound {Call : Type} {k : Nat} {tr : List Call}
    (h : CountedTrace k tr) : tr.length ≤ stage1Budget k := by
  obtain ⟨ts, ls, ps, cs, hperm, ht, hl, hp, hc⟩ := h.pieces
  have he := hperm.length_eq
  simp only [List.length_append] at he
  unfold stage1Budget
  omega

#print axioms Trie.balance
#print axioms plateau_sum_le
#print axioms profile_bound
#print axioms batch_profile_bound
#print axioms stage1Budget_closed
#print axioms stage1Budget_ten
#print axioms batchA_parents
#print axioms batchA_supplied
#print axioms countedTrace_bound
end AspisR1.QvStage1
