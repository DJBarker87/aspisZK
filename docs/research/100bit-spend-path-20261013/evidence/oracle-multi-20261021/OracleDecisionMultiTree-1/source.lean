import OracleDecisionPrereqLog

/-! A shared authentication subtree. Opaque branches are supplied digests,
not oracle calls. Each opened leaf and each occupied parent is hashed once.
Tree traversal is postorder; the Rust level-order scheduling join is separate.
No soundness endpoint or existing module is changed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiTree
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionFeasibilityCore

inductive Tree where
  | supplied (digest : State)
  | opened (input : Bytes)
  | branch (left right : Tree)

def leaves : Tree → Nat
  | .supplied _ => 0
  | .opened _ => 1
  | .branch l r => leaves l + leaves r

def siblings : Tree → Nat
  | .supplied _ => 1
  | .opened _ => 0
  | .branch l r => siblings l + siblings r

def parents : Tree → Nat
  | .supplied _ => 0
  | .opened _ => 0
  | .branch l r => parents l + parents r + 1

def children (l r : State) : BinMerkle32Path.Children := ![l, r]

def root (H : Bytes → State) : Tree → State
  | .supplied d => d
  | .opened a => H a
  | .branch l r => H (BinMerkle32Path.nodeInput (children (root H l) (root H r)))

def execute : Tree → Program Bytes State State
  | .supplied d => .done d
  | .opened a => .ask a fun d => .done d
  | .branch l r => bind (execute l) fun dl => bind (execute r) fun dr =>
      .ask (BinMerkle32Path.nodeInput (children dl dr)) fun d => .done d

/-- Excludes gratuitous hashing of wholly unopened subtrees. -/
def Minimal : Tree → Prop
  | .supplied _ => True
  | .opened _ => True
  | .branch l r => Minimal l ∧ Minimal r ∧ 0 < leaves l + leaves r

theorem binary_count (t : Tree) : parents t + 1 = siblings t + leaves t := by
  induction t with
  | supplied d => rfl
  | opened a => rfl
  | branch l r il ir => simp only [parents, siblings, leaves]; omega

theorem execute_root (H : Bytes → State) (t : Tree) :
    (eval H (execute t)).2 = root H t := by
  induction t with
  | supplied d => rfl
  | opened a => rfl
  | branch l r il ir => simp only [execute, eval_bind, eval, il, ir, root]

theorem execute_length (H : Bytes → State) (t : Tree) :
    (eval H (execute t)).1.length = leaves t + parents t := by
  induction t with
  | supplied d => rfl
  | opened a => rfl
  | branch l r il ir =>
      simp only [execute, eval_bind, eval, List.length_append, List.length_cons,
        List.length_nil, il, ir, leaves, parents]
      omega

structure Commitment where
  tree : Tree
  committed : State

def verifyTrees : List Commitment → Program Bytes State Bool
  | [] => .done true
  | c :: cs => bind (execute c.tree) fun d => bind (verifyTrees cs) fun b =>
      .done (decide (d = c.committed) && b)

def totalLeaves (cs : List Commitment) : Nat := (cs.map fun c => leaves c.tree).sum
def totalParents (cs : List Commitment) : Nat := (cs.map fun c => parents c.tree).sum
def totalSiblings (cs : List Commitment) : Nat := (cs.map fun c => siblings c.tree).sum

theorem forest_count (cs : List Commitment) :
    totalParents cs + cs.length = totalSiblings cs + totalLeaves cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have ht := binary_count c.tree
      simp only [totalParents, totalSiblings, totalLeaves, List.map_cons,
        List.sum_cons, List.length_cons] at *
      omega

theorem verifyTrees_length (H : Bytes → State) (cs : List Commitment) :
    (eval H (verifyTrees cs)).1.length = totalLeaves cs + totalParents cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [verifyTrees, eval_bind, eval, List.append_nil, List.length_append,
        execute_length, ih, totalLeaves, totalParents, List.map_cons, List.sum_cons]
      omega

/-- Duplicate folded indices are checked after hashing all source openings.
`duplicateInputs` accounts for those extra source leaf calls; supplied sibling
nodes themselves are values, never oracle queries. Six checkpoint reads are
kept explicit rather than disguised as free operations. -/
def terminal (cs : List Commitment) (duplicateInputs frames : List Bytes) :
    Program Bytes State Bool :=
  bind (OracleDecisionPrereqPaths.readFrames (frames ++ duplicateInputs)) fun _ => verifyTrees cs

def decision (cs : List Commitment) (duplicateInputs frames : List Bytes) : Decision :=
  fun _ _ => terminal cs duplicateInputs frames

theorem terminal_length (H : Bytes → State) (cs : List Commitment)
    (duplicateInputs frames : List Bytes) :
    (eval H (terminal cs duplicateInputs frames)).1.length =
      frames.length + duplicateInputs.length + totalLeaves cs + totalParents cs := by
  simp only [terminal, eval_bind, List.length_append,
    OracleDecisionPrereqPaths.readFrames_length, verifyTrees_length]
  omega

/-- The parser's fixed slot capacities are checked BEFORE parent hashing.
This covers every query set admitted by the deployed six-slot format, even
if an independent mathematical worst-case bound has not yet been used. -/
def Admissible (cs : List Commitment) (duplicates frames : List Bytes) : Prop :=
  cs.length = 6 ∧ totalSiblings cs ≤ 914 ∧
  totalLeaves cs + duplicates.length = 66 ∧ frames.length = 6

def B_V_multi (sharedNodes distinctLeaves : Nat) : Nat :=
  115 + 6 + 66 + (sharedNodes + distinctLeaves - 6)

theorem closed_count (H : Bytes → State) (cs : List Commitment)
    (duplicates frames : List Bytes) (ha : Admissible cs duplicates frames) :
    115 + (eval H (terminal cs duplicates frames)).1.length =
      B_V_multi (totalSiblings cs) (totalLeaves cs) := by
  have hc := forest_count cs
  rcases ha with ⟨hn, hs, hl, hf⟩
  rw [terminal_length]
  unfold B_V_multi
  omega

theorem budget_bound (cs : List Commitment) (duplicates frames : List Bytes)
    (ha : Admissible cs duplicates frames) :
    B_V_multi (totalSiblings cs) (totalLeaves cs) ≤ 1221 := by
  rcases ha with ⟨hn, hs, hl, hf⟩
  unfold B_V_multi
  omega

theorem verifier_budget (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (ha : Admissible cs duplicates frames) :
    (eval H (verifier D (decision cs duplicates frames) pub pf)).1.length ≤ 1221 := by
  have hc := closed_count H cs duplicates frames ha
  have hb := budget_bound cs duplicates frames ha
  apply (OracleDecisionPrereqSampler.verifier_length D _ H pub pf
    (eval H (terminal cs duplicates frames)).1.length (by exact le_rfl)).trans
  omega

theorem frozen_arithmetic : B_V_multi 914 66 = 1221 ∧ ¬ B_V_multi 914 66 ≤ 1161 := by
  norm_num [B_V_multi]

#print axioms binary_count
#print axioms execute_root
#print axioms execute_length
#print axioms forest_count
#print axioms verifyTrees_length
#print axioms terminal_length
#print axioms closed_count
#print axioms budget_bound
#print axioms verifier_budget
#print axioms frozen_arithmetic
end AspisR1.OracleDecisionMultiTree
end
