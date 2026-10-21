import R4Transport2QueryPrefix
import R4TransportPrefixFrame

/-! Discharge the query chain's absorb-address premise from the successful
source absorb and canonical payload bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4Transport2QueryAbsorb
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem absorb31_address {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (hcall : transcript.Transcript.absorb D before 31#u8 payload = ok absorbed)
    (fits : (R4Transport2OpeningChain.framed payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    H (RawSamplerSuffixCorrespondence.absorption P 31
      (R4Transport2OpeningChain.message payload fits)).toBytes = decodeState absorbed.state := by
  have htag : 160#u8 + 31#u8 = ok 191#u8 := by
    obtain ⟨tag, ht, hv⟩ := WP.spec_imp_exists
      (U8.add_spec (x := 160#u8) (y := 31#u8) (by scalar_tac))
    have he : tag = 191#u8 := by scalar_tac
    simpa only [he] using ht
  rw [CallerStep.opening_absorb_eq D before 31#u8 191#u8 payload
    (UScalar.cast .U32 (Slice.len payload)) htag rfl] at hcall
  obtain ⟨out,hout,he⟩ := bind_success _ _ _ hcall
  have heq : absorbed = {before with state := out} := (Result.ok.inj he).symm
  rw [R4TransportPrefixFrame.absorption_preimage P 31
    (R4Transport2OpeningChain.message payload fits) before.state 191#u8
    (UScalar.cast .U32 (Slice.len payload)) payload hstate
    (by apply Fin.ext; rfl) rfl,heq]
  exact (hdigest before.hash _ out hout).symm

/-- This is the source row31 digest schedule with the selected scan state.
The remaining decoder/caller join must identify the shipped scan result with
this checked single-step driver's result. -/
theorem source_query_prefix {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before absorbed : transcript.Transcript Hash) (payload : Slice U8)
    (hcall : transcript.Transcript.absorb D before 31#u8 payload = ok absorbed)
    (fits : (R4Transport2OpeningChain.framed payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message)
    (hm : LiteralTranscript.erase m = .payload (R4Transport2OpeningChain.message payload fits))
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (blocks states : Nat → Bytes32) (hstart : states 0 = absorbed.state)
    (hs : ∀ k < 8, D.digest absorbed.hash (readParts (states k) 2#u8) = ok (states (k+1)))
    (hb : ∀ k < 8, D.digest absorbed.hash (readParts (states k) 1#u8) = ok (blocks k))
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 31 P m).toProgram).2 =
    UnifiedSampler.liftQuery (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (R4Transport2QueryPrefix.pairs (fun k => decodeState (blocks k))
        (fun k => decodeState (states k))) (decodeState (states 0))) := by
  apply R4Transport2QueryPrefix.source_query_chain D absorbed.hash H P m
    (R4Transport2OpeningChain.message payload fits) hm blocks states
  · rw [hstart]
    exact absorb31_address D before absorbed payload hcall fits P hstate H hdigest
  · exact hs
  · exact hb
  · exact hdigest

#print axioms bind_success
#print axioms absorb31_address
#print axioms source_query_prefix
end AspisR1PublicPreparation.R4Transport2QueryAbsorb
end
