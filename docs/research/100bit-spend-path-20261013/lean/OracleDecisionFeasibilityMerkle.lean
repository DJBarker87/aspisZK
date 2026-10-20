import OracleDecisionFeasibilityBudget
import BinThreeCommitmentTypedOpening

/-! A generic-depth oracle decision supplies its own opening reads.
Collision exclusion is indispensable; see D0OpeningRecoveryObstruction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionFeasibilityMerkle
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler (Public Proof Prover experiment experiment_eval)
open OracleDecisionFeasibilityCore
open BinMerkle32Path BinMerkle32Leaf
attribute [local instance] Classical.propDecidable

def checkPath {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) : Program Bytes State Bool :=
  bind (BinMerkleProgram.leafProgram path leaf) fun computed =>
    .done (decide (computed = root))

def decision {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) : Decision := fun _ _ => checkPath path leaf root

theorem eval_check {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (H : Bytes → State) :
    eval H (checkPath path leaf root) =
      ((eval H (BinMerkleProgram.leafProgram path leaf)).1,
        decide ((eval H (BinMerkleProgram.leafProgram path leaf)).2 = root)) := by
  simp only [checkPath, eval_bind, eval, List.append_nil]

theorem path_trace_length {slots : List (Fin 2)} (path : Path slots)
    (H : Bytes → State) : ∀ current, (inputTrace H path current).length = slots.length := by
  induction path with
  | nil => intro current; rfl
  | cons siblings tail ih =>
    intro current
    simp only [inputTrace, List.length_cons, ih]

theorem check_queries {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (H : Bytes → State) :
    (eval H (checkPath path leaf root)).1.length = slots.length + 1 := by
  rw [eval_check, BinMerkleProgram.eval_leafProgram]
  simp only [List.length_map, fullTrace, List.length_cons, path_trace_length]

/-- These reads are in the actual full experiment, with no source-containment
hypothesis. The preceding prover and sampler traces can be arbitrary. -/
theorem opening_reads {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (D : LiteralByteProtocol.Decoder)
    (P : Prover) (H : Bytes → State) (a : Bytes)
    (ha : Read (eval H (BinMerkleProgram.leafProgram path leaf)).1 a) :
    Read (eval H (original D (decision path leaf root) P)).1 a := by
  unfold original
  rw [RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval]
  change a ∈ ((eval H P).1 ++ (_ ++
    (eval H (checkPath path leaf root)).1)).map Prod.fst
  rw [eval_check]
  simp only [List.map_append, List.mem_append]
  exact Or.inr (Or.inr ha)

theorem accepted_root {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (D : LiteralByteProtocol.Decoder)
    (P : Prover) (H : Bytes → State)
    (hacc : (eval H (original D (decision path leaf root) P)).2.2 = true) :
    (eval H (BinMerkleProgram.leafProgram path leaf)).2 = root := by
  unfold original at hacc
  rw [RawCutProverCompiler.experiment_eval, OracleDecisionFeasibilityBudget.verifier_eval] at hacc
  change (eval H (checkPath path leaf root)).2 = true at hacc
  rw [eval_check] at hacc
  exact of_decide_eq_true hacc

/-- Both previously explicit operational premises, successful recomputation
and containment, now follow from executing the decision. Depth is symbolic.
The frame/root parse, width, salt, budget and non-collision hypotheses remain. -/
theorem accepted_leaf_determined {slots : List (Fin 2)} (path : Path slots)
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32) (root iv : State)
    (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) (Q : Nat)
    (frame : Bytes) (j : Fin 5)
    (hframe : Read (eval H (original D
      (decision path (leafInput tag packed salt) root) P)).1 frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (hQ : firstReads emptyTable (eval H (original D
      (decision path (leafInput tag packed salt) root) P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (original D (decision path (leafInput tag packed salt) root) P)).1)
    (hacc : (eval H (original D
      (decision path (leafInput tag packed salt) root) P)).2.2 = true) :
    BinMerkleLeafRecovery.recover
      (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut
        (eval H (original D (decision path (leafInput tag packed salt) root) P)).1 frame))
      (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut
        (eval H (original D (decision path (leafInput tag packed salt) root) P)).1 frame))
      slots root = some (packed, salt) := by
  exact BinRawByteCutRecovery.recover_at_first_commitment iv H _ Q
    (FS.eval_consistent H _) hQ hout tag width packed salt hw hs path root
    frame j hframe hpred (accepted_root path _ root D P H hacc)
    (opening_reads path _ root D P H)

/-- Recording returns precisely the trace used by the recovery theorem. -/
theorem recorded_log {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (D : LiteralByteProtocol.Decoder)
    (P : Prover) (H : Bytes → State) :
    (eval H (recorded D (decision path leaf root) P)).2.1 =
      (eval H (original D (decision path leaf root) P)).1 := by
  rw [recorded, OracleProgramRecording.eval_record]

#print axioms eval_check
#print axioms path_trace_length
#print axioms check_queries
#print axioms opening_reads
#print axioms accepted_root
#print axioms accepted_leaf_determined
#print axioms recorded_log
end AspisR1.OracleDecisionFeasibilityMerkle
end
