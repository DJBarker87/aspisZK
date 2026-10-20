import RawSamplerSuffixSourceBridge
import ExtractedPreparedModel
import ExtractedSourceSemanticSampler

/-! Row32 source-value and duplex-state transport. Framing and preceding
prefix equality stay explicit; this is not a full frozen caller proof. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4TransportRhoSource
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1 AspisV8R15.ExactTowerBase
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
theorem rho_success {H : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : aspis_core.field.QM31)
    (h : PreparedModel.scalar_k B D self row payload = ok (out,after)) :
    ∃ block, transcript.Transcript.block D self row payload = ok (block,after) ∧
      sampler.qm31_sample block = ok out := by
  unfold PreparedModel.scalar_k at h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨block,mid,hblock,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
  obtain ⟨wide,hwide,h⟩ := bind_success _ _ _ h
  obtain ⟨mark,htrace,h⟩ := bind_success _ _ _ h
  cases mark
  have he := Result.ok.inj h
  have hv : value = out := congrArg Prod.fst he
  have ht : mid = after := congrArg Prod.snd he
  exact ⟨block,by simpa only [ht] using hblock,by simpa only [hv] using hvalue⟩


#print axioms bind_success
#print axioms pair_bind_success
#print axioms rho_success

def decodeQM (q : aspis_core.field.QM31) : QM31Exact :=
  ExtractedCurrentQM31Exact.decode
    (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q))

/-- All 256-bit inputs succeed, including words >= P; there is no retry. -/
theorem qm31_total_model (block : Bytes32) :
    ∃ q : aspis_core.field.QM31,
      sampler.qm31_sample block = ok q ∧
      decodeQM q = R0P.SemSource.qm31Sample (decodeState block) := by
  obtain ⟨q, hq, _, _⟩ := SamplerTransport.sample_total block
  exact ⟨q, hq, SourceSemanticSampler.sample_qm31 block q hq⟩

/-- The actual returned rho, embedded into the ordinary carrier, equals the
selected model sampler, with exactly the same returned transcript state. -/
theorem rho_call_transport {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self after : transcript.Transcript Hash)
    (payload : Slice U8) (q : aspis_core.field.QM31)
    (hcall : PreparedModel.scalar_k B D self 32#u8 payload = ok (q, after))
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (b : SelectedTranscriptParams.Message) (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (n : U32) (hlen : UScalar.cast .U32 (Slice.len payload) = n)
    (hbytes : SelectedTranscriptParams.params.enc b =
      PublicInitFrame.lengthBytes n.val ++ rawBytes payload)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 32 P m).toProgram).2 =
      (.ordinary (algebraMap QM31Exact AspisWideTower.WideExact (decodeQM q)),
        decodeState after.state) := by
  obtain ⟨block, hb, hq⟩ := rho_success B D self after 32#u8 payload q hcall
  have ht := SamplerSuffixSourceBridge.opening_block_correspondence D self after
    32#u8 192#u8 payload n block hb (by rfl) hlen P 32 (by omega)
    (by rfl) m b hm hstate hbytes H hdigest
  have hv : SelectedChallengeMap.sigma 32 (decodeState block) =
      algebraMap QM31Exact AspisWideTower.WideExact (decodeQM q) := by
    simpa only [SelectedChallengeMap.sigma, show (32 : Nat) ≠ 27 by decide,
      show ¬ ((32 : Nat) = 28 ∨ 32 = 29 ∨ 32 = 30) by decide,
      show (32 : Nat) ≠ 31 by decide, if_false, decodeQM] using
      (SourceSemanticSampler.sample_semChal block q hq).symm
  rw [hv] at ht
  exact ht

#print axioms qm31_total_model
#print axioms rho_call_transport
end AspisR1PublicPreparation.R4TransportRhoSource
end
