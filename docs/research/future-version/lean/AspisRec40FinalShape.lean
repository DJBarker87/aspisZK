import AspisRec40CleanStatement
import R1LiteralByteRunFacts

/-! The premise on rows 33 to 39 that the decoding of those rows needs, and
the retained counterexample to the earlier hypothesis without it.

`LatePayload pf`: the messages of rows 33 to 39 erase to payload messages, so
the sampler treats each of them as a plain row (`UnifiedSampler.samp` on
`.payload`). This is the weakest form the decoding uses: the 64-byte frame and
canonical decoding are not needed for decoding, only for the checks.
`latePayload_of_checks`: it follows from an `AspisChecks` value on the
40-row transcript (`decode33`, `entryRound`: `decodePairS` succeeds only on a
payload message). `latePayload_enrich`: it is invariant under the word
enrichment of the charged proof.

Counterexample (reviewer, ef4cd439a53): `finalDecodes_fails_initial`. If row 35
carries `.initial`, the sampler of row 35 is `invalid p`, whose first cell is
the squeeze frame of the initial vector, which `decFinal` never decodes; so
`FinalDecodes` fails on such a run, while R1's four premises (`hQ`, `hout`,
`format`, `tag`) do not constrain row 35. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalShape
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment
open AspisR1

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-- The premise: rows 33 to 39 are payload rows. -/
def LatePayload (pf : LiteralProtocol.Proof) : Prop :=
  ∀ i, 33 ≤ i → i < 40 → ∃ b, LiteralTranscript.erase (pf i) = .payload b

theorem payload_of_decode (m : LiteralTranscript.Message) (x : AspisAcceptance.EW × AspisAcceptance.EW)
    (h : AspisOneTx.decodePairS m = some x) : ∃ b, LiteralTranscript.erase m = .payload b := by
  unfold AspisOneTx.decodePairS at h
  cases he : LiteralTranscript.erase m with
  | initial r => rw [he] at h; simp [AspisRows40.Protocol.payloadOf] at h
  | payload b => exact ⟨b, rfl⟩

theorem latePayload_enrich (w : CanonicalCutEnrichedTranscript.Words) (pf : LiteralProtocol.Proof) :
    LatePayload (RawCutTranscriptRun.proof w pf) ↔ LatePayload pf := by
  unfold LatePayload RawCutTranscriptRun.proof
  simp only [CanonicalCutEnrichedTranscript.erase_enrichMessage]

/-- Row i's message in the 40-row transcript is `pf i`. -/
theorem entry_message (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (i : Nat) (hi : i < 40)
    (m : LiteralTranscript.Message) (ch : LiteralTranscript.Challenge)
    (h : ((pr D).transcript H pub pf 40).rounds[i]? = some (m, ch)) : m = pf i := by
  rw [AspisRows40.Protocol.transcript_eq] at h
  have hi' := LiteralByteRunFacts.transcript_index D H pub pf 40 i hi
  rw [h] at hi'
  exact congrArg Prod.fst (Option.some.inj hi')

/-- The premise from an `AspisChecks` value on the run's 40-row transcript. -/
theorem latePayload_of_checks (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (c : AspisAcceptance.AspisChecks AspisOneTx.decodePairS pub
      ((pr D).transcript H pub pf 40).rounds) : LatePayload pf := by
  intro i hlo hhi
  by_cases h33 : i = 33
  · subst h33
    have hm := entry_message D H pub pf 33 (by decide) _ _ c.entry33
    rw [← hm]
    exact payload_of_decode _ _ c.decode33
  · obtain ⟨mb, vb, sb, he, hd, _⟩ := c.entryRound (i - 34) (by omega)
    rw [show 34 + (i - 34) = i by omega] at he
    have hm := entry_message D H pub pf i hhi _ _ he
    rw [← hm]
    exact payload_of_decode _ _ hd

/-- Non-vacuity of the premise: any proof whose rows 33 to 39 are payload
messages (the honest prover's, `Protocol.finalMessage`) satisfies it. -/
theorem latePayload_of_payloads (pf : LiteralProtocol.Proof)
    (h : ∀ i, 33 ≤ i → i < 40 → ∃ b, pf i = .payload b) : LatePayload pf := by
  intro i hlo hhi
  obtain ⟨b, hb⟩ := h i hlo hhi
  exact ⟨b, by rw [hb]; rfl⟩

/-- Retained counterexample: a run whose row-35 message is `.initial` does not
satisfy `FinalDecodes` (row 35's first cell is the squeeze frame of the
initial vector, never decoded by `decFinal`). -/
theorem finalDecodes_fails_initial (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (v : RawCutProverCompiler.RunView) (r : State) (w : LiteralTranscript.C1Word)
    (h35 : v.2.1.2 35 = .initial r w) :
    ¬ AspisRec40.CleanStatement.FinalDecodes D H v := by
  intro hf
  have hfc : firstCell ((pr D).chain H v.2.1.1 v.2.1.2 35) =
      some (squeezeA SelectedTranscriptParams.params SelectedTranscriptParams.params.iv).toBytes := by
    change firstCell (LiteralByteSampler.samp 35 _ (v.2.1.2 35)) = _
    rw [h35]
    rfl
  obtain ⟨own, pend, g, hd, _⟩ := hf 35 _ (by decide) (by decide) hfc
  have hn := AspisRows40.Starts.aspis_squeeze AspisRows40.FinalByte.fin
    SelectedTranscriptParams.params.iv
    (tableBefore emptyTable v.1
      (squeezeA SelectedTranscriptParams.params SelectedTranscriptParams.params.iv).toBytes)
  change AspisRows40.Starts.decAspis AspisRows40.FinalByte.fin _ _ = _ at hd
  rw [hn] at hd
  cases hd

#print axioms payload_of_decode
#print axioms latePayload_enrich
#print axioms entry_message
#print axioms latePayload_of_checks
#print axioms latePayload_of_payloads
#print axioms finalDecodes_fails_initial

end AspisRec40.FinalShape
end
