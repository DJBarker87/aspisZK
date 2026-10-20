import OracleDecisionMultiTree

/-! Every opened leaf has a path through the shared execution. The path is
constructed from the shared tree, not rehashed. All its query addresses are
already in that execution. Collision-free log recovery can therefore reuse
the generic-depth cut-recovery theorem with no independent-path reads. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiRecovery
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionMultiTree BinMerkle32Path

/-- Append one parent at the root end of a leaf-to-root path. -/
def extend {slots : List (Fin 2)} (p : Path slots) (slot : Fin 2) (cs : Children) :
    Path (slots ++ [slot]) :=
  match p with
  | .nil => .cons cs .nil
  | .cons ss tail => .cons ss (extend tail slot cs)

theorem fold_extend {slots : List (Fin 2)} (p : Path slots) (slot : Fin 2)
    (cs : Children) (H : Bytes → State) (d : State) :
    foldPath H (extend p slot cs) d = H (nodeInput (fillChild slot cs (foldPath H p d))) := by
  induction p generalizing d with
  | nil => rfl
  | cons ss tail ih => exact ih _

theorem trace_extend {slots : List (Fin 2)} (p : Path slots) (slot : Fin 2)
    (cs : Children) (H : Bytes → State) (d : State) :
    inputTrace H (extend p slot cs) d = inputTrace H p d ++
      [nodeInput (fillChild slot cs (foldPath H p d))] := by
  induction p generalizing d with
  | nil => rfl
  | cons ss tail ih =>
      simp only [extend, inputTrace, foldPath, ih, List.cons_append]

/-- Root-to-leaf route, retaining the public binary position. -/
inductive OpenedAt : Tree → List (Fin 2) → Bytes → Prop where
  | leaf (a : Bytes) : OpenedAt (.opened a) [] a
  | left {l r : Tree} {slots : List (Fin 2)} {a : Bytes} :
      OpenedAt l slots a → OpenedAt (.branch l r) (0 :: slots) a
  | right {l r : Tree} {slots : List (Fin 2)} {a : Bytes} :
      OpenedAt r slots a → OpenedAt (.branch l r) (1 :: slots) a

def inputs (H : Bytes → State) : Tree → List Bytes
  | .supplied _ => []
  | .opened a => [a]
  | .branch l r => inputs H l ++ inputs H r ++ [nodeInput (children (root H l) (root H r))]

theorem execute_inputs (H : Bytes → State) (t : Tree) :
    ((eval H (execute t)).1.map Prod.fst) = inputs H t := by
  induction t with
  | supplied d => rfl
  | opened a => rfl
  | branch l r il ir =>
      simp only [execute, eval_bind, eval, List.map_append, List.map_cons,
        List.map_nil, execute_root, il, ir, inputs, List.append_assoc]

theorem fill_children_left (l r : State) : fillChild 0 (children l r) l = children l r := by
  simp [fillChild, children]

theorem fill_children_right (l r : State) : fillChild 1 (children l r) r = children l r := by
  simp [fillChild, children]

/-- A path witness uses only addresses already hashed by the shared program. -/
theorem shared_path (H : Bytes → State) {t : Tree} {slots : List (Fin 2)} {a : Bytes}
    (ho : OpenedAt t slots a) :
    ∃ p : Path slots.reverse,
      foldPath H p (H a) = root H t ∧
      ∀ b ∈ BinMerkle32Leaf.fullTrace H p a, b ∈ inputs H t := by
  induction ho with
  | leaf a =>
      exact ⟨.nil, rfl, by intro b hb; exact hb⟩
  | @left l r slots a ho ih =>
      obtain ⟨p, hp, ht⟩ := ih
      rw [List.reverse_cons]
      refine ⟨extend p 0 (children (root H l) (root H r)), ?_, ?_⟩
      · rw [fold_extend, hp, fill_children_left]; rfl
      · intro b hb
        simp only [BinMerkle32Leaf.fullTrace, trace_extend, hp, fill_children_left,
          List.mem_append, List.mem_singleton, List.mem_cons] at hb
        rcases hb with hb | hb | hb
        · subst b
          have h := ht a (List.mem_cons_self ..)
          simp only [inputs, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inl h)
        · have h := ht b (List.mem_cons_of_mem _ hb)
          simp only [inputs, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inl h)
        · subst b
          simp [inputs]
  | @right l r slots a ho ih =>
      obtain ⟨p, hp, ht⟩ := ih
      rw [List.reverse_cons]
      refine ⟨extend p 1 (children (root H l) (root H r)), ?_, ?_⟩
      · rw [fold_extend, hp, fill_children_right]; rfl
      · intro b hb
        simp only [BinMerkle32Leaf.fullTrace, trace_extend, hp, fill_children_right,
          List.mem_append, List.mem_singleton, List.mem_cons] at hb
        rcases hb with hb | hb | hb
        · subst b
          have h := ht a (List.mem_cons_self ..)
          simp only [inputs, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr h)
        · have h := ht b (List.mem_cons_of_mem _ hb)
          simp only [inputs, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr h)
        · subst b
          simp [inputs]

theorem verifyTrees_roots (H : Bytes → State) (cs : List Commitment)
    (ha : (eval H (verifyTrees cs)).2 = true) :
    ∀ c ∈ cs, root H c.tree = c.committed := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      simp only [verifyTrees, eval_bind, eval, execute_root, Bool.and_eq_true,
        decide_eq_true_eq] at ha
      intro x hx
      rcases List.mem_cons.mp hx with he | ht
      · subst x; exact ha.1
      · exact ih ha.2 x ht

theorem verifyTrees_reads (H : Bytes → State) (cs : List Commitment)
    (c : Commitment) (hc : c ∈ cs) (b : Bytes) (hb : b ∈ inputs H c.tree) :
    Read (eval H (verifyTrees cs)).1 b := by
  induction cs with
  | nil => simp at hc
  | cons x xs ih =>
      simp only [verifyTrees, eval_bind, eval, List.append_nil]
      change b ∈ (((eval H (execute x.tree)).1 ++ (eval H (verifyTrees xs)).1).map Prod.fst)
      rw [List.map_append, List.mem_append]
      rcases List.mem_cons.mp hc with he | ht
      · subst x; exact Or.inl (by rwa [execute_inputs])
      · exact Or.inr (ih ht)

theorem original_reads (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : RawCutProverCompiler.Prover)
    (c : Commitment) (hc : c ∈ cs) (b : Bytes) (hb : b ∈ inputs H c.tree) :
    Read (eval H (original D (decision cs duplicates frames) P)).1 b := by
  rw [original, RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval]
  change b ∈ ((_ ++ (_ ++ (eval H (terminal cs duplicates frames)).1)).map Prod.fst)
  simp only [terminal, eval_bind, List.map_append, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (verifyTrees_reads H cs c hc b hb)))

theorem accepted_roots (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : RawCutProverCompiler.Prover)
    (ha : (eval H (original D (decision cs duplicates frames) P)).2.2 = true) :
    ∀ c ∈ cs, root H c.tree = c.committed := by
  rw [original, RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval] at ha
  change (eval H (terminal cs duplicates frames)).2 = true at ha
  apply verifyTrees_roots H cs
  simpa only [terminal, eval_bind] using ha

/-- Generic-depth leaf recovery from the actual shared decision's log.
Only root-frame parsing, width/salt and collision-budget premises remain;
success and trace containment follow from executing the shared decision. -/
theorem accepted_leaf_recovery (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : RawCutProverCompiler.Prover)
    (c : Commitment) (hc : c ∈ cs) (slots : List (Fin 2))
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (ho : OpenedAt c.tree slots (BinMerkle32Leaf.leafInput tag packed salt))
    (hw : packed.length = width) (hs : salt.length = 32) (iv : State) (Q : Nat)
    (frame : Bytes) (j : Fin 5)
    (hframe : Read (eval H (original D (decision cs duplicates frames) P)).1 frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some c.committed)
    (hQ : firstReads emptyTable (eval H (original D (decision cs duplicates frames) P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (original D (decision cs duplicates frames) P)).1)
    (hacc : (eval H (original D (decision cs duplicates frames) P)).2.2 = true) :
    BinMerkleLeafRecovery.recover
      (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut
        (eval H (original D (decision cs duplicates frames) P)).1 frame))
      (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut
        (eval H (original D (decision cs duplicates frames) P)).1 frame))
      slots.reverse c.committed = some (packed, salt) := by
  obtain ⟨path, hp, ht⟩ := shared_path H ho
  apply BinRawByteCutRecovery.recover_at_first_commitment iv H _ Q
    (FS.eval_consistent H _) hQ hout tag width packed salt hw hs path c.committed
    frame j hframe hpred
  · rw [BinMerkleProgram.eval_leafProgram]
    exact hp.trans (accepted_roots D H cs duplicates frames P hacc c hc)
  · intro b hb
    rw [BinMerkleProgram.eval_leafProgram] at hb
    change b ∈ ((BinMerkle32Leaf.fullTrace H path _).map (fun a => (a, H a))).map Prod.fst at hb
    simp only [List.map_map, Function.comp_def, List.map_id] at hb
    exact original_reads D H cs duplicates frames P c hc b (ht b hb)

#print axioms fold_extend
#print axioms trace_extend
#print axioms execute_inputs
#print axioms fill_children_left
#print axioms fill_children_right
#print axioms shared_path
#print axioms verifyTrees_roots
#print axioms verifyTrees_reads
#print axioms original_reads
#print axioms accepted_roots
#print axioms accepted_leaf_recovery
end AspisR1.OracleDecisionMultiRecovery
end
