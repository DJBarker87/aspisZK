import LiteralLegacyVerifierTrace
import RawBoundedProgram
import LiteralDecoderPrefixRestore
import AspisRec40FinalRun
import AspisRec40FinalLiteral
import AspisRows40Protocol

/-! Rows 0 to 39 of the literal byte protocol as R1's address-level unified
run, under R1's validity of rows 0 to 32 and the literal late-row premise
(`FinalLiteral.LateLiteral`: rows 33 to 39 are `.payload b`).

Copies of R1's `LiteralLegacyRun.message_eq`, `erased_transcript_eq`,
`chain_eval_eq` (33 → 40), `LiteralLegacyVerifierTrace.trace_eq_map` /
`restricted_trace_eq` with the 40-row verifiers (byte: `AspisRows40.Protocol`;
address: `AspisRec40.FinalRun`), and `LiteralDecoderPrefixRestore.actual_prefix`
with the restored word list equal to the enrichment words (rows 33 to 39 are
payload rows, which the restore and the enrichment both leave as payloads). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalLegacy
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 LiteralLegacyRun
open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript

abbrev p := SelectedTranscriptParams.params
theorem hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]

/-- R1's validity below row 33 and the literal premise at rows 33 to 39. -/
def Valid40 (pf : Proof) : Prop :=
  (∀ i < 33, LiteralTranscript.valid i (pf i)) ∧ FinalLiteral.LateLiteral pf

theorem message_eq40 (pf : Proof) (hv : Valid40 pf) (i : Nat) (hi : i < 40) :
    LiteralTranscript.erase (pf i) = legacyProtocol.msg (proof pf) i := by
  by_cases h33 : i < 33
  · exact LiteralLegacyRun.message_eq pf hv.1 i h33
  · obtain ⟨b, hb⟩ := hv.2 i (by omega) hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    change LiteralTranscript.erase (pf (j + 1)) = .payload (bytesOf (pf (j + 1)))
    rw [hb]
    rfl

theorem erased_transcript_eq40 (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof) (hv : Valid40 pf)
    (n : Nat) (hn : n ≤ 40) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) =
      legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change LiteralTranscript.erasePrefix
        (((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext (pf n)
          (eval H (LiteralByteSampler.samp n
            ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n)).toProgram).2) = _
      rw [LiteralTranscript.erasePrefix_ext, LiteralByteSampler.eval_eq]
      change (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).ext
        (LiteralTranscript.erase (pf n))
        (eval (fun a => H a.toBytes) (UnifiedSampler.samp SelectedTranscriptParams.params _ n
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol decoder).transcript H pub pf n))
          (LiteralTranscript.erase (pf n))).toProgram).2 =
        (legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n).ext
          (legacyProtocol.msg (proof pf) n)
          (eval (fun a => H a.toBytes) (legacyProtocol.samp n
            (legacyProtocol.transcript (fun a => H a.toBytes) pub (proof pf) n)
            (legacyProtocol.msg (proof pf) n)).toProgram).2
      rw [ih (by omega), message_eq40 pf hv n (by omega)]
      rfl

theorem chain_eval_eq40 (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof) (hv : Valid40 pf)
    (i : Nat) (hi : i < 40) :
    eval H ((LiteralByteProtocol.protocol decoder).chain H pub pf i).toProgram =
      mapView Addr.toBytes
        (eval (fun a => H a.toBytes)
          (legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i).toProgram) := by
  change eval H (LiteralByteSampler.samp i
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf i) (pf i)).toProgram = _
  rw [LiteralByteSampler.eval_eq]
  unfold LiteralTranscript.samp
  rw [erased_transcript_eq40 decoder H pub pf hv i (by omega), message_eq40 pf hv i hi]
  rfl

private theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem chain_firstCell_eq40 (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof) (hv : Valid40 pf)
    (n : Nat) (hn : n < 40) :
    firstCell ((AspisRows40.Protocol.protocol decoder).chain H pub pf n) =
      (firstCell (legacyProtocol.chain (fun b => H b.toBytes) pub (proof pf) n)).map Addr.toBytes := by
  rw [AspisRows40.Protocol.chain_eq]
  change firstCell (ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp n
    ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n))) = _
  rw [firstCell_map]
  unfold LiteralTranscript.samp
  rw [erased_transcript_eq40 decoder H pub pf hv n (by omega), message_eq40 pf hv n hn]
  rfl

/-- The legacy chain of a row `n ≥ 1` starts at row n's absorb frame. -/
theorem legacy_firstCell (H : Addr SelectedTranscriptParams.L → State)
    (pub : LiteralTranscript.Public) (π : UnifiedProtocol.Proof LiteralTranscript.BytesMessage)
    (n : Nat) (h0 : n ≠ 0) (h26 : n ≠ 26) (h31 : n ≠ 31) :
    firstCell (legacyProtocol.chain H pub π n) =
      some (UnifiedSteps.address p hD H pub π.1 π.2 n) := by
  rw [legacyProtocol, UnifiedProtocol.chain_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  change firstCell (UnifiedSampler.samp p _ (j + 1) _ (.payload (π.2 (j + 1)))) = _
  rw [UnifiedSampler.row_ordinary p _ (j + 1) h0 h26 h31]
  change some (UnifiedSampler.absorb p (j + 1) _ _) = _
  rw [UnifiedSteps.payload_address p hD H pub π.1 π.2 (j + 1) h0]

/-- The 40-row byte verifier's trace, restricted to canonical addresses, is
the 40-row address-level verifier's trace. -/
theorem restricted_trace_eq40 {W : Type} (decoder : LiteralByteProtocol.Decoder)
    (draw : LiteralTranscript.Prefix → LiteralTranscript.Message → Bool)
    (extract : UnifiedSampler.Public SelectedTranscriptParams.L →
      Table (Addr SelectedTranscriptParams.L) State → Option W)
    (dold : UnifiedSampler.Prefix LiteralTranscript.BytesMessage AspisWideTower.WideExact
      SelectedTranscriptParams.L → TranscriptView.Message LiteralTranscript.BytesMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : Proof) (hv : Valid40 pf) :
    RawBoundedTrace.trace SelectedTranscriptParams.L
      (eval H (FS2.verifier (AspisRows40.Protocol.protocol decoder) draw pub pf)).1 =
      (eval (fun a => H a.toBytes)
        (AspisRec40.FinalRun.verifier p hD extract dold pub (proof pf))).1 := by
  have hmap : (eval H (FS2.verifier (AspisRows40.Protocol.protocol decoder) draw pub pf)).1 =
      (eval (fun a => H a.toBytes)
        (AspisRec40.FinalRun.verifier p hD extract dold pub (proof pf))).1.map
          fun q => (q.1.toBytes, q.2) := by
    unfold AspisRec40.FinalRun.verifier
    rw [FS2.verifier_eval, FS2.verifier_eval]
    change ((List.range 40).map fun i =>
      (eval H ((AspisRows40.Protocol.protocol decoder).chain H pub pf i).toProgram).1).flatten =
      (((List.range 40).map fun i =>
        (eval (fun a => H a.toBytes)
          ((AspisRec40.FinalRun.protocol p hD extract).chain (fun a => H a.toBytes) pub
            (proof pf) i).toProgram).1).flatten.map fun q => (q.1.toBytes, q.2))
    rw [List.map_flatten, List.map_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have hc : (AspisRec40.FinalRun.protocol p hD extract).chain (fun a => H a.toBytes) pub
        (proof pf) i = legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i := by
      rw [AspisRec40.FinalRun.chain_eq, legacyProtocol, UnifiedProtocol.chain_eq]
      rfl
    simp only [Function.comp_apply]
    rw [AspisRows40.Protocol.chain_eq, hc]
    exact congrArg Prod.fst (chain_eval_eq40 decoder H pub pf hv i (List.mem_range.mp hi))
  rw [hmap]
  apply RawBoundedProgram.trace_map_canonical
  intro q hq
  unfold AspisRec40.FinalRun.verifier at hq
  rw [FS2.verifier_eval] at hq
  simp only [List.mem_flatten, List.mem_map] at hq
  obtain ⟨tr, ⟨i, _, he⟩, hmem⟩ := hq
  subst tr
  have hc : (AspisRec40.FinalRun.protocol p hD extract).chain (fun a => H a.toBytes) pub
      (proof pf) i = legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i := by
    rw [AspisRec40.FinalRun.chain_eq, legacyProtocol, UnifiedProtocol.chain_eq]
    rfl
  rw [hc] at hmem
  exact RawBoundedProgram.labels_eval CanonicalByteAddress.Canonical
    (legacyProtocol.chain (fun a => H a.toBytes) pub (proof pf) i).toProgram
    (LiteralLegacyVerifierTrace.chain_canonical (fun a => H a.toBytes) pub (proof pf) i)
    (fun a => H a.toBytes) q hmem

/-- Restore of one valid or late-payload row. -/
theorem message_restore (w : Words) (i : Nat) (m : LiteralTranscript.Message)
    (h : LiteralTranscript.valid i m ∨ (33 ≤ i ∧ ∃ b, m = .payload b)) :
    message w i (LiteralTranscript.erase m) = enrichMessage w m := by
  rcases h with h | ⟨hi, b, rfl⟩
  · exact message_of_valid w i m h
  · simp only [LiteralTranscript.erase, message, if_neg (by omega : i ≠ 2),
      if_neg (by omega : i ≠ 30)]
    rfl

/-- Copy of `LiteralDecoderPrefixRestore.actual_prefix` (33 → 40), with the
restore words equal to the enrichment words. -/
theorem actual_prefix40 (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (hv : Valid40 pf) (W : Words) (n : Nat) (hn : n ≤ 40) :
    restorePrefix W (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)) =
      enrichPrefix W ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change restorePrefix W (LiteralTranscript.erasePrefix
        (((LiteralByteProtocol.protocol decoder).transcript H pub pf n).ext (pf n)
          ((LiteralByteProtocol.protocol decoder).chal H pub pf n))) = _
      rw [LiteralTranscript.erasePrefix_ext, LiteralDecoderPrefixRestore.prefix_ext]
      rw [ih (by omega)]
      have hr : (LiteralTranscript.erasePrefix
          ((LiteralByteProtocol.protocol decoder).transcript H pub pf n)).round = n := by
        rw [LiteralTranscript.erasePrefix_round, FS2.transcript_round]
      have hok : LiteralTranscript.valid n (pf n) ∨ (33 ≤ n ∧ ∃ b, pf n = .payload b) := by
        by_cases h33 : n < 33
        · exact Or.inl (hv.1 n h33)
        · exact Or.inr ⟨by omega, hv.2 n (by omega) (by omega)⟩
      rw [hr, message_restore W n (pf n) hok]
      exact (RawCutTranscriptRun.prefix_ext W
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf n) (pf n)
        ((LiteralByteProtocol.protocol decoder).chal H pub pf n)).symm

#print axioms message_eq40
#print axioms erased_transcript_eq40
#print axioms chain_eval_eq40
#print axioms chain_firstCell_eq40
#print axioms legacy_firstCell
#print axioms restricted_trace_eq40
#print axioms message_restore
#print axioms actual_prefix40

end AspisRec40.FinalLegacy
end
