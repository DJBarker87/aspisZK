import OracleDecisionFeasibilityCompiler
import OracleDecisionFeasibilityMerkle

/-! Recovery on the compiled experiment itself, rather than a detached trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionFeasibilityBridge
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open CanonicalCutEnrichedTranscript (Words)
open OracleDecisionFeasibilityCore
open OracleDecisionFeasibilityCompiler (compiled)
open OracleDecisionFeasibilityMerkle
open BinMerkle32Path BinMerkle32Leaf

def annotated (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (buildWords : RunView → Words) (P : Prover) :=
  experiment (compiled D dO buildWords P) (verifier D dO)

theorem opening_reads_compiled {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (D : LiteralByteProtocol.Decoder)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State)
    (a : Bytes) (ha : Read (eval H (BinMerkleProgram.leafProgram path leaf)).1 a) :
    Read (eval H (annotated D (decision path leaf root) buildWords P)).1 a := by
  unfold annotated
  rw [OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  change a ∈ ((_ : List (Bytes × State)) ++ _).map Prod.fst
  rw [List.map_append]
  exact List.mem_append.mpr (Or.inl (opening_reads path leaf root D P H a ha))

/-- No opening-containment or standalone opening-success premise is supplied:
both follow from the oracle decision in the compiled run. -/
theorem compiled_leaf_determined {slots : List (Fin 2)} (path : Path slots)
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32) (root iv : State)
    (D : LiteralByteProtocol.Decoder) (buildWords : RunView → Words)
    (P : Prover) (H : Bytes → State) (Q : Nat) (frame : Bytes) (j : Fin 5)
    (hframe : Read (eval H (annotated D
      (decision path (leafInput tag packed salt) root) buildWords P)).1 frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root)
    (hQ : firstReads emptyTable (eval H (annotated D
      (decision path (leafInput tag packed salt) root) buildWords P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (annotated D
        (decision path (leafInput tag packed salt) root) buildWords P)).1)
    (hacc : (eval H (annotated D
      (decision path (leafInput tag packed salt) root) buildWords P)).2.2 = true) :
    BinMerkleLeafRecovery.recover
      (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut
        (eval H (annotated D
          (decision path (leafInput tag packed salt) root) buildWords P)).1 frame))
      (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut
        (eval H (annotated D
          (decision path (leafInput tag packed salt) root) buildWords P)).1 frame))
      slots root = some (packed, salt) := by
  have he := (OracleDecisionFeasibilityCompiler.public_and_acceptance D
    (decision path (leafInput tag packed salt) root) buildWords P H).2
  have haccOrig : (eval H (original D
      (decision path (leafInput tag packed salt) root) P)).2.2 = true := he ▸ hacc
  exact BinRawByteCutRecovery.recover_at_first_commitment iv H _ Q
    (FS.eval_consistent H _) hQ hout tag width packed salt hw hs path root frame j
    hframe hpred (accepted_root path _ root D P H haccOrig)
    (opening_reads_compiled path _ root D buildWords P H)

/-- A single eighteen-level path costs nineteen terminal queries and fits the
existing envelope, even with the deliberately coarse 561 sampler allowance. -/
theorem single_path_budget {slots : List (Fin 2)} (path : Path slots)
    (leaf : Bytes) (root : State) (D : LiteralByteProtocol.Decoder)
    (P : Prover) (Q : Nat) (H : Bytes → State)
    (hprover : (eval H P).1.length ≤ Q) (hdepth : slots.length ≤ 599) :
    firstReads emptyTable (eval H (original D (decision path leaf root) P)).1 ≤ Q + 1161 := by
  apply OracleDecisionFeasibilityBudget.original_reads D (decision path leaf root) P Q
    (slots.length + 1) H hprover
  · intro pub pf
    exact (check_queries path leaf root H).le
  · omega

#print axioms opening_reads_compiled
#print axioms compiled_leaf_determined
#print axioms single_path_budget
end AspisR1.OracleDecisionFeasibilityBridge
end
