import OraclePortRowAwareObstructionD8

/-! Exact false zero-start subclaim, including the causal gate and the
binary no-collision hypothesis. No accepted-frozen-source claim is made. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareCounterclaimD9
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionMultiDecoder OraclePortRowAwareWitnessD2
open OraclePortRowAwareGateWitnessD5 OraclePortRowAwareNoCollisionD6
open OraclePortRowAwareCausalD1 OraclePortRowAwareObstructionD8
open DecodedFirstReadUnionBound

theorem causal_clean_zero_is_false (D : LiteralByteProtocol.Decoder) (Q : Nat) :
    ¬ (∀ (prior : List (Bytes × State)) (cs : BinMerkle32Path.Children),
      let a := OracleDecisionDomSepFrozen.node cs
      let T := applyTrace emptyTable prior
      Gate D a T →
      ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred Q) emptyTable (prior ++ [(a,fun _ => 6)]) →
      decoderFirstReads (decode D) T [(a,fun _ => 6)] = 0) := by
  intro h
  have hz := h past (OracleDecisionMultiTree.children zero right)
  dsimp only at hz
  rw [← frozen_node,cached_table] at hz
  have he := hz (gate_node D) (clean_no_collision Q)
  rw [terminal_start D] at he
  cases he

#print axioms causal_clean_zero_is_false
end AspisR1.OraclePortRowAwareCounterclaimD9
end
