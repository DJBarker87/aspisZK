import OracleDecisionPrereqPaths
import BinInitialQueryAccounting

/-! Starts are recognised fresh decoder inputs, not only initial frames.
This module separates the unconditional bound from the zero-terminal-start
condition. Compiler replay adds no starts for any terminal decision. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqStarts
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore
open DecodedFirstReadUnionBound
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

/-- Exactly the compiler-shaped experiment; not the self-recorder wrapper. -/
def annotated (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) :=
  RawCutProverCompiler.experiment (OracleDecisionFeasibilityCompiler.compiled D dO words P)
    (verifier D dO)

theorem compiler_starts (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D dO words P)).1 =
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (original D dO P)).1 := by
  rw [annotated, OracleDecisionFeasibilityCompiler.compiled_experiment_eval]
  unfold original
  rw [RawCutProverCompiler.experiment_eval]
  exact decoderFirstReads_repeat_suffix _ _ _

theorem verifier_starts (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (T : Table Bytes State) (N : Nat)
    (hterminal : ∀ U : Table Bytes State,
      decoderFirstReads RecordedBinaryExperimentBin.dec U
        (eval H (onBytes dO ((LiteralByteProtocol.protocol D).transcript H pub pf 33)
          (pf 33))).1 ≤ N) :
    decoderFirstReads RecordedBinaryExperimentBin.dec T
      (eval H (verifier D dO pub pf)).1 ≤ 34 + N := by
  rw [OracleDecisionFeasibilityBudget.verifier_eval, decoderFirstReads_append]
  have hs := BinHonestQueryBudget.rows_bound D H pub pf (List.range 33) List.nodup_range T
  have hs' : decoderFirstReads RecordedBinaryExperimentBin.dec T
      (((List.range 33).map fun n =>
        (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1).flatten) ≤ 34 :=
    hs.trans (by norm_num)
  exact Nat.add_le_add hs' (hterminal _)

theorem recorded_starts (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q N : Nat)
    (hq : (eval H P).1.length ≤ Q)
    (hterminal : ∀ pub pf (T : Table Bytes State),
      decoderFirstReads RecordedBinaryExperimentBin.dec T
        (eval H (onBytes dO ((LiteralByteProtocol.protocol D).transcript H pub pf 33)
          (pf 33))).1 ≤ N) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D dO words P)).1 ≤ Q + 34 + N := by
  rw [compiler_starts, original, RawCutProverCompiler.experiment_eval, decoderFirstReads_append]
  have hp := (DecoderQueryAccounting.starts_le_queries RecordedBinaryExperimentBin.dec
    emptyTable (eval H P).1).trans hq
  have hv := verifier_starts D dO H (eval H P).2.1 (eval H P).2.2
    (applyTrace emptyTable (eval H P).1) N (hterminal _ _)
  omega

/-- A valid sufficient condition, stronger than excluding initial frames. -/
theorem retain_Q_add_34 (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q)
    (hzero : ∀ pub pf (T : Table Bytes State),
      decoderFirstReads RecordedBinaryExperimentBin.dec T
        (eval H (onBytes dO ((LiteralByteProtocol.protocol D).transcript H pub pf 33)
          (pf 33))).1 = 0) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D dO words P)).1 ≤ Q + 34 := by
  exact recorded_starts D dO words P H Q 0 hq (fun pub pf T => (hzero pub pf T).le)

/-- Unconditional bound for every path/frame input; no byte-domain separation
or initialisation-only charging assumption is silently introduced. -/
theorem independent_paths_starts (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1 ≤
      Q + 34 + (frames.length + OracleDecisionPrereqPaths.pathCalls os) := by
  apply recorded_starts D _ words P H Q _ hq
  intro pub pf T
  exact (DecoderQueryAccounting.starts_le_queries _ _ _).trans_eq
    (OracleDecisionPrereqPaths.terminal_length os frames H)

theorem frozen_starts (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (words : RunView → Words) (P : Prover) (H : Bytes → State) (Q : Nat)
    (hq : (eval H P).1.length ≤ Q) (hc : os.length = 66)
    (hd : ∀ o ∈ os, o.slots.length = 18) (hf : frames.length = 6) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (annotated D (OracleDecisionPrereqPaths.decision os frames) words P)).1 ≤ Q + 1294 := by
  have hb := independent_paths_starts D os frames words P H Q hq
  rw [OracleDecisionPrereqPaths.pathCalls_uniform os 18 hd, hc, hf] at hb
  omega

/-- Literal initial frames start with 85. This exclusion alone is NOT an
exclusion from RecordedBinaryExperimentBin.dec, which dispatches other rows. -/
theorem not_initial_of_head (a : Bytes) (hhead : a.head? ≠ some (85 : AspisV8R19.DuplexFrames.Byte)) :
    ¬ BinInitialQueryAccounting.CanonicalInitial a := by
  rintro ⟨pub, root, _, _, he⟩
  change a = (PublicInitFrame.addr pub.pubBytes pub.initFits root).toBytes at he
  rw [PublicInitFrame.addr_bytes] at he
  have hh := congrArg List.head? he
  apply hhead
  simpa [PublicInitFrame.domain] using hh

theorem leaf_not_initial (tag : BinMerkle32Path.Byte) (packed salt : Bytes) :
    ¬ BinInitialQueryAccounting.CanonicalInitial (BinMerkle32Leaf.leafInput tag packed salt) := by
  apply not_initial_of_head
  simp [BinMerkle32Leaf.leafInput]

theorem node_not_initial (children : BinMerkle32Path.Children) :
    ¬ BinInitialQueryAccounting.CanonicalInitial (BinMerkle32Path.nodeInput children) := by
  apply not_initial_of_head
  simp [BinMerkle32Path.nodeInput]

/-- The feasibility interface accepts arbitrary frame bytes. Such an extra
read can itself be an initial frame; six arbitrary extra reads cannot be
assigned zero starts without a source-level framing theorem. -/
theorem arbitrary_frame_can_start (pub : LiteralTranscript.Public) (root : State)
    (hlen : pub.pubBytes.length < 2^32) (htag : pub.tag = 2) (H : Bytes → State) :
    decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (OracleDecisionPrereqPaths.readFrames
        [CanonicalAddressEmbedding.toBytes (BinDecoderInitialStarts.initialAddress pub root)])).1 = 1 := by
  have hd := BinDecoderInitialStarts.recognizes_initial pub root hlen htag
    (emptyTable : Table Bytes State)
  simp only [OracleDecisionPrereqPaths.readFrames, eval, decoderFirstReads,
    emptyTable, hd, ne_eq, not_false_eq_true, and_self, if_true, Nat.add_zero]

#print axioms compiler_starts
#print axioms verifier_starts
#print axioms recorded_starts
#print axioms retain_Q_add_34
#print axioms independent_paths_starts
#print axioms frozen_starts
#print axioms not_initial_of_head
#print axioms leaf_not_initial
#print axioms node_not_initial
#print axioms arbitrary_frame_can_start
end AspisR1.OracleDecisionPrereqStarts
end
