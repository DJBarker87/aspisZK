import BinCheckedPublicSelection

/-! Additive C3 handoff: clean words are derived; known-public table decoder
completion and operational source laws remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinM9C3Closure
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun R1FinalSoundness
open BinChecksAdaptiveFailureNoModel BinDecoderCompletionBoundary

/-- Every binary parent is rejected by the historical eight-way node parser.
This prevents treating the two recovery adapters as a definitional rename. -/
theorem binary_node_old_parser_rejects (cs : BinMerkle32Path.Children) :
    MerkleNodeCodec.parse (BinMerkle32Path.nodeInput cs) = none := by
  have hne : Merkle32Path.nodeInput
      (MerkleNodeCodec.readChildren (BinMerkle32Path.nodeInput cs)) ≠
      BinMerkle32Path.nodeInput cs := by
    intro h
    have hl := congrArg List.length h
    rw [Merkle32Path.nodeInput_length, BinMerkle32Path.nodeInput_length] at hl
    omega
  unfold MerkleNodeCodec.parse
  exact if_neg hne

/-- Explicit counterexample to universal parser identification: even the
binary node with both child digests zero has different parser success. -/
theorem parser_identification_false :
    ¬ (∀ input : Bytes,
      (MerkleNodeCodec.parse input).isSome = (BinMerkleNodeCodec.parse input).isSome) := by
  intro h
  let cs : BinMerkle32Path.Children := fun _ _ => 0
  have hh := h (BinMerkle32Path.nodeInput cs)
  rw [binary_node_old_parser_rejects, BinMerkleNodeCodec.parse_nodeInput] at hh
  cases hh

/-- Supplies precisely final_soundness's h_R12_binary_words using its existing
R19 and R-wire inputs, once its own hchecks has been constructed. -/
theorem c3_binary_words_obligation
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (s : BoundaryStatements)
    (hQ : BoundaryEvidence s → ∀ H : Bytes → State,
      firstReads emptyTable (eval H (original D d P)).1 ≤ Q + 1161)
    (hwire : BoundaryEvidence s → BinaryCompletion D d P (Q + 1161)) :
    BoundaryEvidence s → CheckedAcceptance D d P → BinaryClean D d P (Q + 1161) := by
  intro evidence hchecks
  exact binaryClean_of_checked_acceptance D d P (Q + 1161)
    (hQ evidence) hchecks (hwire evidence)

/-- Binary model endpoint with the public-selector half of completion
discharged. Its only remaining decoder law is the exact known-public
LiteralCompletion, including the historical table WordChoice. -/
theorem composed_binary_failure_bound_known_public
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (deployedFailure : ℚ)
    (hQ : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (original D d P)).1 ≤ Q + 1161)
    (htag : ∀ H : Bytes → State, (eval H (original D d P)).2.1.1.tag = 2)
    (hchecks : CheckedAcceptance D d P)
    (hknown : LiteralCompletion D d P (Q + 1161))
    (hN : ∀ H : Bytes → State, DecodedFirstReadUnionBound.decoderFirstReads dec
      emptyTable (eval H (recorded D d P)).1 ≤ 33)
    (htransport : DeployedTransport D d P deployedFailure) :
    BinaryClean D d P (Q + 1161) ∧
    deployedFailure ≤ R1FinalSoundnessNumeric.totalBound Q ∧
    (Q ≤ R1FinalSoundnessNumeric.maxAdversaryQueries →
      deployedFailure < 1 / (2 : ℚ)^100) := by
  have hcompletion := (BinCheckedPublicSelection.binaryCompletion_iff_known_public
    D d P (Q + 1161) hQ htag hchecks).2 hknown
  exact composed_binary_failure_bound D d P Q deployedFailure
    hQ hchecks hcompletion hN htransport

#print axioms binary_node_old_parser_rejects
#print axioms parser_identification_false
#print axioms c3_binary_words_obligation
#print axioms composed_binary_failure_bound_known_public
end AspisR1.BinM9C3Closure
end
