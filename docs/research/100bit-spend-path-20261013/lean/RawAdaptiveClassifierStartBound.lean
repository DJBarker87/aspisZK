import DecodedFirstReadTraceBridge

/-! Apply the direct classifier density to actual decoder-start counts,
retaining a concrete trace-budget obligation. This does not prove that any
arbitrary prover has at most 33 starts. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawAdaptiveClassifierStartBound
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open DecodedFirstReadUnionBound RawAdaptiveClassifierHitDensity

/-- Shared-oracle classifier-hit mass is bounded by the actual number of
recognized fresh chain starts, rather than by all internal hash calls. The
trace count includes every prover and verifier read in exp. -/
theorem shared_hit_mass_le_starts
    {Pf : Type}
    (pubChoice : RawAdaptiveLiteralDecoder.PublicChoice)
    (words : RawLiteralDecoderDensity.WordChoice)
    (exp : Program Bytes State (Pf × Bool)) (N : Nat)
    (hN : ∀ H : Bytes → State,
      decoderFirstReads (RawAdaptiveLiteralDecoder.decode pubChoice words)
        emptyTable (eval H exp).1 ≤ N) :
    lazyMean exp emptyTable (fun run => indicator
      (hitsChain3 (RawAdaptiveLiteralDecoder.decode pubChoice words)
        classifier emptyTable run.1)) ≤ (N : ℚ) * PerAttemptEnvelope.B := by
  apply decoded_first_read_bound
      (RawAdaptiveLiteralDecoder.decode pubChoice words) classifier
      PerAttemptEnvelope.B exp emptyTable N
  · unfold PerAttemptEnvelope.B
    positivity
  · exact adaptive_decoded_classifier_le pubChoice words
  · apply decoderReadsBound_of_traces
    exact hN

/-- Scalar feasibility after, and only after, a concrete one-attempt
experiment has established its 33-start budget. The separate shared collision
mass may be as large as 2^-120; no hash-work/grinding credit appears. -/
theorem thirty_three_start_envelope_lt_100
    (N : Nat) (hN : N ≤ 33) (collisionMass : ℚ)
    (hcollision : collisionMass ≤ 1 / (2 : ℚ)^120) :
    (N : ℚ) * PerAttemptEnvelope.B + collisionMass + 1 / (2 : ℚ)^126 <
      1 / (2 : ℚ)^100 := by
  have hn : (N : ℚ) ≤ 33 := by exact_mod_cast hN
  have hb : 0 ≤ PerAttemptEnvelope.B := by unfold PerAttemptEnvelope.B; positivity
  have hs : (33 : ℚ) * PerAttemptEnvelope.B + 1 / (2 : ℚ)^120 +
      1 / (2 : ℚ)^126 < 1 / (2 : ℚ)^100 := by
    unfold PerAttemptEnvelope.B
    norm_num
  apply lt_of_le_of_lt _ hs
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hn hb) hcollision) le_rfl

#print axioms shared_hit_mass_le_starts
#print axioms thirty_three_start_envelope_lt_100
end AspisR1.RawAdaptiveClassifierStartBound
end
