import RawSamplerSuffixCorrespondence
import RawSamplerSuffixSourceFrames

/-! Local source-to-literal bridge for the non-query, non-reseed suffix rows.
The source digest interpretation is explicit; no functional oracle is
constructed by overwriting repeated addresses. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SamplerSuffixSourceBridge
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1 AspisR1.RawSamplerSuffixCorrespondence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Applies to gamma/kappa/alpha0/alpha1/rho after success inversion with
OpeningCalls.scalar_success/rho_success. The output arithmetic interpretation
is deliberately separate from this exact state/challenge-block theorem. -/
theorem opening_block_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : transcript.Transcript Hash) (row tag : U8)
    (payload : Slice U8) (n : U32) (block : Bytes32)
    (hcall : transcript.Transcript.block D self row payload = ok (block, after))
    (htag : 160#u8 + row = ok tag)
    (hlen : UScalar.cast .U32 (Slice.len payload) = n)
    (P : LiteralTranscript.Prefix) (i : Nat)
    (hi : i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 32)
    (hlabel : SelectedTranscriptParams.params.lbl i = decodeByte tag)
    (m : LiteralTranscript.Message) (b : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b =
      AspisR1.PublicInitFrame.lengthBytes n.val ++ rawBytes payload)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp i P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma i (decodeState block)),
        decodeState after.state) := by
  obtain ⟨absorbed, next, ha, hb, hn, he⟩ :=
    CallerStep.opening_block_success D self after row payload block hcall
  rw [CallerStep.opening_absorb_eq D self row tag payload n htag hlen] at ha
  obtain ⟨s, hs, heAbs⟩ := bind_success _ _ _ ha
  have heAbs' : absorbed = {self with state := s} := (Result.ok.inj heAbs).symm
  have hframe : (absorption P i b).toBytes =
      flatten (CallerStep.openingAbsorbParts self.state tag n payload) := by
    unfold absorption UnifiedSampler.absorb
    rw [hstate, hlabel, absorbA, Addr.toBytes_ofBytes,
      SamplerSuffixSourceFrames.opening_absorb_frame, hbytes]
    rfl
  apply RawSamplerSuffixCorrespondence.ordinary_correspondence
    (fun a : Addr SelectedTranscriptParams.L => H a.toBytes) P i
    (by omega) m b hm (decodeState absorbed.state) (decodeState block)
    (decodeState after.state)
  · rw [hframe, heAbs']
    exact (hdigest self.hash _ s hs).symm
  · rw [← squeeze_address SelectedTranscriptParams.params absorbed.state]
    exact (hdigest absorbed.hash _ block hb).symm
  · rw [← advance_address SelectedTranscriptParams.params absorbed.state, he]
    exact (hdigest absorbed.hash _ next hn).symm

/-- The semantic circle call exposes the same three source digest reads.
This theorem deliberately stops before row 26's additional constructor. -/
theorem circle_block_reads {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : r1_wire.SemanticTranscript Hash) (row : U8)
    (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D self row payload =
      ok (.Ok block, after))
    (hrow : row.val = 25 ∨ row.val = 26)
    (P : LiteralTranscript.Prefix) (b : SelectedTranscriptParams.Message)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b = rawBytes payload)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    ∃ absorbed : State,
      H (absorption P row.val b).toBytes = absorbed ∧
      H (squeezeA SelectedTranscriptParams.params absorbed).toBytes = decodeState block ∧
      H (advanceA SelectedTranscriptParams.params absorbed).toBytes = decodeState after.state := by
  obtain ⟨_, tag, next, absorbed, state, ht, _, ha, hb, hn, he⟩ :=
    TranscriptStep.step_success D self after row payload block (by omega) hcall
  have hlabel : SelectedTranscriptParams.params.lbl row.val = decodeByte tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label row.val).val = decodeByte tag
    rw [SelectedTranscriptParams.label_val row.val (by omega)]
    exact ht.symm
  have hframe : (absorption P row.val b).toBytes = flatten (absorbParts self.state tag payload) := by
    unfold absorption UnifiedSampler.absorb
    rw [hstate, hlabel, absorbA, Addr.toBytes_ofBytes, flatten_absorb, hbytes]
    rfl
  refine ⟨decodeState absorbed, ?_, ?_, ?_⟩
  · rw [hframe]
    exact (hdigest self.hash _ absorbed ha).symm
  · rw [← squeeze_address SelectedTranscriptParams.params absorbed]
    exact (hdigest self.hash _ block hb).symm
  · rw [← advance_address SelectedTranscriptParams.params absorbed, he]
    exact (hdigest self.hash _ state hn).symm

/-- Row 25: exact circle-parameter challenge and carried semantic state. -/
theorem circle25_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D self 25#u8 payload =
      ok (.Ok block, after))
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (b : SelectedTranscriptParams.Message) (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b = rawBytes payload)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 25 P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 25 (decodeState block)), decodeState after.state) := by
  obtain ⟨a, ha, hb, hn⟩ := circle_block_reads D self after 25#u8 payload block hcall
    (by decide) P b hstate hbytes H hdigest
  exact RawSamplerSuffixCorrespondence.ordinary_correspondence _ P 25
    (by omega) m b hm a (decodeState block) (decodeState after.state) ha hb hn

/-- Row 26: the challenge comes from the circle call, whereas the carried
state comes from Transcript.new on that call's returned semantic state. -/
theorem circle26_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D self 26#u8 payload =
      ok (.Ok block, after))
    (hash : Hash) (variant : transport.Variant) (opening : transcript.Transcript Hash)
    (hnew : transcript.Transcript.new D hash after.state variant = ok opening)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (b : SelectedTranscriptParams.Message) (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b = rawBytes payload)
    (htag : P.statement.tag = decodeByte (CallerStep.variantTag variant))
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 26 P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 26 (decodeState block)), decodeState opening.state) := by
  obtain ⟨a, ha, hb, hn⟩ := circle_block_reads D self after 26#u8 payload block hcall
    (by decide) P b hstate hbytes H hdigest
  apply RawSamplerSuffixCorrespondence.reseed_correspondence _ P m b hm
    a (decodeState block) (decodeState after.state) (decodeState opening.state) ha hb hn
  rw [OpeningReseedFrame.addr, Addr.toBytes_ofBytes, htag]
  exact (SamplerSuffixSourceFrames.reseed_state D hash after.state variant opening H hnew
    (fun out ho => hdigest hash _ out ho)).symm

#print axioms bind_success
#print axioms circle_block_reads
#print axioms circle25_correspondence
#print axioms circle26_correspondence
#print axioms opening_block_correspondence
end AspisR1PublicPreparation.SamplerSuffixSourceBridge
end
