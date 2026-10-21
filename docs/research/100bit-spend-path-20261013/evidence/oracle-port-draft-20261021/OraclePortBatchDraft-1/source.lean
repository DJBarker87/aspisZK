import OraclePortSelectedDraft

/-! Shared tree execution retains the leaf digests for duplicate checks.
Exactly the nonrepresentative openings incur an additional leaf call. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortBatchDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OracleDecisionMultiTree
open OraclePortCompactDraft OraclePortSelectedDraft
attribute [local instance] Classical.propDecidable

/-- Retain the digests produced during the actual shared tree execution. -/
def execute : Tree → Program Bytes State (State × List (Bytes × State))
  | .supplied d => .done (d,[])
  | .opened a => .ask a fun d => .done (d,[(a,d)])
  | .branch l r => bind (execute l) fun dl => bind (execute r) fun dr =>
      .ask (BinMerkle32Path.nodeInput (children dl.1 dr.1)) fun d => .done (d,dl.2++dr.2)

theorem execute_trace (H : Bytes → State) (t : Tree) :
    (eval H (execute t)).1 = (eval H (OracleDecisionMultiTree.execute t)).1 ∧
    (eval H (execute t)).2.1 = root H t := by
  induction t with
  | supplied d => exact ⟨rfl,rfl⟩
  | opened a => exact ⟨rfl,rfl⟩
  | branch l r il ir =>
    simp only [execute, OracleDecisionMultiTree.execute, eval_bind, eval,
      il.1, ir.1, il.2, ir.2, execute_root, root]
    exact ⟨rfl,rfl⟩

theorem retained_consistent (H : Bytes → State) (t : Tree) :
    ∀ a ∈ (eval H (execute t)).2.2, a.2 = H a.1 := by
  induction t with
  | supplied d => simp [execute,eval]
  | opened a => simp [execute,eval]
  | branch l r il ir =>
    simp only [execute,eval_bind,eval]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact il a ha
    · exact ir a ha

def duplicatePositions (q : Fin 22 → Fin 262144) (batch kind : Nat) : List Nat :=
  (batchPositions batch).filter (fun pos => decide (pos ≠ position q batch kind (index q kind pos)))

/-- Equality is checked on digests, as in batch_tree, without strengthening
it to a byte equality that would reject a source-accepted collision run. -/
def duplicates (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (known : List (Bytes × State)) : List Nat → Program Bytes State Bool
  | [] => .done true
  | pos::rest => .ask (leaf p kind pos) fun d =>
      bind (duplicates p q batch kind known rest) fun ok =>
        .done (decide (known.lookup (input p q batch kind (index q kind pos)) = some d) && ok)

def committedRoot (p : Parsed) (kind : Nat) : State :=
  let b := if kind = 0 then root0 p else if kind = 1 then
    ((p.semantic[2]?.getD []).drop 5) else root2 p
  (SemanticRecordCodec.decodeState b).getD (fun _ => 0)

def verifySlot (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    Program Bytes State Bool :=
  bind (execute (tree p q batch kind)) fun out =>
    bind (duplicates p q batch kind out.2 (duplicatePositions q batch kind)) fun ok =>
      .done (decide (out.1 = committedRoot p kind) && ok)

def verifySlots (p : Parsed) (q : Fin 22 → Fin 262144) :
    List (Nat × Nat) → Program Bytes State Bool
  | [] => .done true
  | (batch,kind)::rest => bind (verifySlot p q batch kind) fun ok =>
      bind (verifySlots p q rest) fun tail => .done (ok && tail)

def slots : List (Nat × Nat) := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)]

/-- This is a parser-and-multiproof decision, not the complete dV. It lacks
semantic/folding/accumulator checks and physical checkpoint replay. -/
def decision : OraclePortExperiment.Decision := fun tr m =>
  match parseTerminal tr m, queries tr with
  | some p, some q => if Padding p q then verifySlots p q slots else .done false
  | _, _ => .done false

theorem slot_root (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (ha : (eval H (verifySlot p q batch kind)).2 = true) :
    root H (tree p q batch kind) = committedRoot p kind := by
  simp only [verifySlot,eval_bind,eval,Bool.and_eq_true,decide_eq_true_eq] at ha
  rw [← (execute_trace H (tree p q batch kind)).2]
  exact ha.1

theorem duplicates_length (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (known : List (Bytes × State)) (ps : List Nat) :
    (eval H (duplicates p q batch kind known ps)).1.length = ps.length := by
  induction ps with
  | nil => rfl
  | cons pos rest ih =>
    simp only [duplicates,eval,eval_bind,List.length_cons,List.length_append,List.length_nil,ih]
    omega

#print axioms execute_trace
#print axioms retained_consistent
#print axioms slot_root
#print axioms duplicates_length
end AspisR1.OraclePortBatchDraft
end
