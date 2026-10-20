import OracleDecisionMultiBuild

/-! Sparse symbolic maximum profiles. The full 2^18-leaf domain is never
expanded. Ten/twelve opened stubs occupy all eight bottom pairs of a
four-level skeleton; unary paths below them supply the remaining siblings.
For folded indices, two extra unary levels pad the 2^16 domain to 2^18. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiProfile
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionMultiTree

def pad : Nat → Tree → Tree
  | 0, t => t
  | n+1, t => .branch (pad n t) (.supplied 0)

theorem pad_counts (n : Nat) (t : Tree) :
    leaves (pad n t) = leaves t ∧ siblings (pad n t) = siblings t + n ∧
    parents (pad n t) = parents t + n := by
  induction n with
  | zero => simp [pad]
  | succ n ih => simp only [pad, leaves, siblings, parents, ih.1, ih.2.1, ih.2.2]; omega

def single (n : Nat) : Tree := .branch (pad n (.opened [])) (.supplied 0)
def double (n : Nat) : Tree := .branch (pad n (.opened [])) (pad n (.opened []))
def four (a b c d : Tree) : Tree := .branch (.branch a b) (.branch c d)
def top10 (n : Nat) : Tree := .branch
  (four (double n) (double n) (single n) (single n))
  (four (single n) (single n) (single n) (single n))
def top12 (n : Nat) : Tree := .branch
  (four (double n) (double n) (double n) (double n))
  (four (single n) (single n) (single n) (single n))

theorem top10_counts (n : Nat) :
    leaves (top10 n) = 10 ∧ siblings (top10 n) = 10*n+6 ∧ parents (top10 n) = 10*n+15 := by
  simp only [top10, four, single, double, leaves, siblings, parents,
    (pad_counts n (.opened [])).1, (pad_counts n (.opened [])).2.1,
    (pad_counts n (.opened [])).2.2]
  constructor <;> try constructor <;> omega

theorem top12_counts (n : Nat) :
    leaves (top12 n) = 12 ∧ siblings (top12 n) = 12*n+4 ∧ parents (top12 n) = 12*n+15 := by
  simp only [top12, four, single, double, leaves, siblings, parents,
    (pad_counts n (.opened [])).1, (pad_counts n (.opened [])).2.1,
    (pad_counts n (.opened [])).2.2]
  constructor <;> try constructor <;> omega

/-- C1A,C2A,foldedA,C1B,C2B,foldedB, in compact slot order. -/
def peak : List Commitment :=
  [⟨top10 14,0⟩, ⟨top10 14,0⟩, ⟨pad 2 (top10 12),0⟩,
   ⟨top12 14,0⟩, ⟨top12 14,0⟩, ⟨pad 2 (top12 12),0⟩]

theorem peak_counts : totalSiblings peak = 914 ∧ totalLeaves peak = 66 ∧
    totalParents peak = 974 := by
  simp only [peak, totalSiblings, totalLeaves, totalParents, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, (pad_counts 2 (top10 12)).1,
    (pad_counts 2 (top10 12)).2.1, (pad_counts 2 (top10 12)).2.2,
    (pad_counts 2 (top12 12)).1, (pad_counts 2 (top12 12)).2.1,
    (pad_counts 2 (top12 12)).2.2, (top10_counts 14).1, (top10_counts 14).2.1,
    (top10_counts 14).2.2, (top10_counts 12).1, (top10_counts 12).2.1,
    (top10_counts 12).2.2, (top12_counts 14).1, (top12_counts 14).2.1,
    (top12_counts 14).2.2, (top12_counts 12).1, (top12_counts 12).2.1,
    (top12_counts 12).2.2]
  norm_num

theorem peak_admissible : Admissible peak [] (List.replicate 6 []) := by
  refine ⟨rfl, peak_counts.1.le, ?_, ?_⟩
  · simpa using peak_counts.2.1
  · simp

theorem peak_calls (H : Bytes → State) :
    115 + (eval H (terminal peak [] (List.replicate 6 []))).1.length = 1161 := by
  rw [closed_count H peak [] _ peak_admissible, peak_counts.1, peak_counts.2.1,
    frozen_arithmetic]

/-- Success is compositional and never evaluates the concrete shared tree. -/
theorem roots_success (H : Bytes → State) (cs : List Commitment)
    (hr : ∀ c ∈ cs, root H c.tree = c.committed) :
    (eval H (verifyTrees cs)).2 = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [verifyTrees, eval_bind, execute_root, eval,
        hr c (by simp), ih (fun x hx => hr x (by simp [hx])), decide_true, Bool.true_and]

theorem terminal_success (H : Bytes → State) (cs : List Commitment)
    (duplicates frames : List Bytes) (hr : ∀ c ∈ cs, root H c.tree = c.committed) :
    (eval H (terminal cs duplicates frames)).2 = true := by
  simpa only [terminal, eval_bind] using roots_success H cs hr

theorem peak_roots : ∀ c ∈ peak, root (fun _ => (0 : State)) c.tree = c.committed := by
  intro c hc
  simp only [peak, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h <;> subst c <;> rfl

attribute [local irreducible] peak terminal

/-- Constant-oracle accepted profile, constructed without kernel replay. -/
theorem peak_accepts : (eval (fun _ => (0 : State))
    (terminal peak [] (List.replicate 6 []))).2 = true :=
  terminal_success _ peak [] _ peak_roots

#print axioms pad_counts
#print axioms top10_counts
#print axioms top12_counts
#print axioms peak_counts
#print axioms peak_admissible
#print axioms peak_calls
#print axioms roots_success
#print axioms terminal_success
#print axioms peak_roots
#print axioms peak_accepts
end AspisR1.OracleDecisionMultiProfile
end
