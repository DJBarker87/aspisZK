import AspisRec40FinalShape
import AspisRec40ChargePrefix
import R16CanonReduction

/-! The late-row premise on the literal constructor, derived from
`FinalShape.LatePayload` (stated on the erased message) and the R16
canonicalisation of the charged base run.

`LatePayload` alone does not fix the literal constructor: `.c2 b w` and
`.second b w` also erase to `.payload b`, and a literal `.c2` at a late row is
restored by the decoder as `.payload b`, so the byte-level bridge (W4,
`FinalBridgeStatement.DecodesAndFollows40`) needs `pf i = .payload b`. The
base run's proof is `R16CanonReduction.proof` of the prover's proof
(`ChargePrefix.prover_eval`), which maps every non-initial message to
`.payload` at rows other than 2 and 30; word enrichment keeps `.payload`. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalLiteral
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment
open AspisR1

/-- The late-row premise on the literal constructor. -/
def LateLiteral (pf : LiteralProtocol.Proof) : Prop :=
  ∀ i, 33 ≤ i → i < 40 → ∃ b, pf i = .payload b

/-- R16's canonical message at a row other than 2 and 30 is `.payload` when
the erased message is. -/
theorem canon_message_payload (i : Nat) (h2 : i ≠ 2) (h30 : i ≠ 30)
    (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (h : LiteralTranscript.erase m = .payload b) :
    R16CanonReduction.message i m = .payload b := by
  cases m with
  | initial r w => cases h
  | payload b' => cases h; simp [R16CanonReduction.message, h2, h30]
  | c2 b' w => cases h; simp [R16CanonReduction.message, h2, h30]
  | second b' w => cases h; simp [R16CanonReduction.message, h2, h30]

/-- On a canonical proof, the erased premise gives the literal one. -/
theorem lateLiteral_of_canon (pf : LiteralProtocol.Proof)
    (h : FinalShape.LatePayload (R16CanonReduction.proof pf)) :
    LateLiteral (R16CanonReduction.proof pf) := by
  intro i hlo hhi
  obtain ⟨b, hb⟩ := h i hlo hhi
  rw [R16CanonReduction.erase_proof] at hb
  exact ⟨b, canon_message_payload i (by omega) (by omega) (pf i) b hb⟩

/-- Word enrichment keeps the literal premise. -/
theorem lateLiteral_enrich (w : CanonicalCutEnrichedTranscript.Words) (pf : LiteralProtocol.Proof)
    (h : LateLiteral pf) : LateLiteral (RawCutTranscriptRun.proof w pf) := by
  intro i hlo hhi
  obtain ⟨b, hb⟩ := h i hlo hhi
  exact ⟨b, by
    change CanonicalCutEnrichedTranscript.enrichMessage w (pf i) = _
    rw [hb]; rfl⟩

/-- The base run's proof is R16-canonical. -/
theorem base_proof (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) :
    (eval H (ChargePrefix.base D P)).2.1.2 =
      R16CanonReduction.proof (eval H P).2.proof := by
  unfold ChargePrefix.base
  rw [RawCutProverCompiler.experiment_eval, ChargePrefix.prover_eval]

/-- The literal premise for the base run, from `LatePayload` on it. -/
theorem base_literal (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (h : FinalShape.LatePayload (eval H (ChargePrefix.base D P)).2.1.2) :
    LateLiteral (eval H (ChargePrefix.base D P)).2.1.2 := by
  rw [base_proof] at h ⊢
  exact lateLiteral_of_canon _ h

/-- The literal premise for the charged run, from `LatePayload` on the base run. -/
theorem charged_literal (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (h : FinalShape.LatePayload (eval H (ChargePrefix.base D P)).2.1.2) :
    LateLiteral (eval H (ChargePrefix.charged D P)).2.1.2 := by
  rw [ChargePrefix.charged_eval]
  exact lateLiteral_enrich _ _ (base_literal D P H h)

#print axioms canon_message_payload
#print axioms lateLiteral_of_canon
#print axioms lateLiteral_enrich
#print axioms base_proof
#print axioms base_literal
#print axioms charged_literal

end AspisRec40.FinalLiteral
end
