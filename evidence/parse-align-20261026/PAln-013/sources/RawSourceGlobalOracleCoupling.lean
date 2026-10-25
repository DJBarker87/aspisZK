import RawSourceDigestLog
import RawSourceLiteralTraceLift

/-! Couple reached source calls to one global byte oracle. No equality of the
constructed source oracle on unqueried addresses is required. The actual global
log embedding and consistency remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceGlobalOracleCoupling
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.TranscriptView
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisR1PublicPreparation.SourceDigestLog
open AspisR1.LiteralTranscript AspisR1.SelectedTranscriptParams
open AspisV8R15.ExactTowerBase AspisV8R19.R599CanonicalFieldTuple

abbrev sourceChallenge := @SourceLiteralTraceLift.sourceChallenge

/-- Actual retained source outputs, interpreted at their three reached byte
addresses by containment in the same consistent global log. -/
theorem call_functional_from_log
    {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (params : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (c : SourceFull25.Call D pre) (hc : c ∈ cs)
    (Hbytes : Bytes → State) (tr : List (Bytes × State))
    (hsource : sourceLog cs ⊆ tr) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (hbound : (rawBytes c.record.framed).length ≤ params.D) :
    decodeState c.absorbed = Hbytes (absorbA params (decodeState c.before.state)
      (decodeByte c.tag) (rawBytes c.record.framed) hbound).toBytes ∧
    decodeState c.block = Hbytes (squeezeA params (decodeState c.absorbed)).toBytes ∧
    decodeState c.after.state = Hbytes (advanceA params (decodeState c.absorbed)).toBytes := by
  have ha := hcons _ (hsource (sourceLog_absorb_mem cs c hc))
  have h1 := hcons (flatten (TranscriptStep.readParts c.absorbed 1#u8),decodeState c.block)
    (hsource (List.mem_flatMap.mpr ⟨c,hc,by simp [callLog]⟩))
  have h2 := hcons (flatten (TranscriptStep.readParts c.absorbed 2#u8),decodeState c.state)
    (hsource (List.mem_flatMap.mpr ⟨c,hc,by simp [callLog]⟩))
  change decodeState c.absorbed = Hbytes (flatten _) at ha
  rw [absorb_address params _ _ _ hbound] at ha
  change decodeState c.block = Hbytes (flatten _) at h1
  rw [squeeze_address params] at h1
  change decodeState c.state = Hbytes (flatten _) at h2
  rw [advance_address params] at h2
  refine ⟨ha,h1,?_⟩
  rw [c.carried]
  exact h2

/-- A reached positive source row equals the literal payload sampler under the
same globally logged oracle, using no all-address source-oracle premise. -/
theorem call_simulates_literal_payload
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (c : SourceFull25.Call D pre) (hc : c ∈ cs)
    (Hbytes : Bytes → State) (tr : List (Bytes × State))
    (hsource : sourceLog cs ⊆ tr) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (hD : ∀ d ∈ cs, (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.D)
    (i : Nat) (hi : i < 25) (hi0 : i ≠ 0) (hrow : c.row.val = i)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (mm : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = TranscriptView.Message.payload mm)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState c.before.state)
    (hbytes : SelectedTranscriptParams.params.enc mm = rawBytes c.record.framed) :
    Value.ordinary (sourceChallenge c) =
      (AspisV8R19.MemoizedProgramLaw.eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (LiteralTranscript.samp i P m).toProgram).2.1 ∧
    decodeState c.after.state =
      (AspisV8R19.MemoizedProgramLaw.eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (LiteralTranscript.samp i P m).toProgram).2.2 := by
  have hbound : (rawBytes c.record.framed).length ≤ SelectedTranscriptParams.params.D :=
    hD c hc
  have htag : SelectedTranscriptParams.params.lbl i = decodeByte c.tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label i).val = decodeByte c.tag
    rw [SelectedTranscriptParams.label_val i (by omega)]
    calc
      160 + i = 160 + c.row.val := by rw [hrow]
      _ = c.tag.val := by
        rw [← c.record_row]
        exact c.tag_code.symm
      _ = decodeByte c.tag := rfl
  have habsorb : absorbA SelectedTranscriptParams.params
      (decodeState c.before.state) (decodeByte c.tag)
      (rawBytes c.record.framed) hbound =
      UnifiedSampler.absorb SelectedTranscriptParams.params i
        (LiteralTranscript.erasePrefix P) mm := by
    unfold UnifiedSampler.absorb
    rw [hstate, htag]
    congr 1
    exact hbytes.symm
  have htrace := call_functional_from_log SelectedTranscriptParams.params cs c hc
    Hbytes tr hsource hcons hbound
  have habsVal : decodeState c.absorbed =
      Hbytes (absorbA SelectedTranscriptParams.params
        (decodeState c.before.state) (decodeByte c.tag)
        (rawBytes c.record.framed) hbound).toBytes := htrace.1
  have hblock : decodeState c.block =
      Hbytes (squeezeA SelectedTranscriptParams.params
        (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
          (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes := by
    rw [← habsorb, ← habsVal]
    exact htrace.2.1
  have hnext : decodeState c.after.state =
      Hbytes (advanceA SelectedTranscriptParams.params
        (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
          (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes := by
    rw [← habsorb, ← habsVal]
    exact htrace.2.2
  have hq := AspisR1PublicPreparation.SourceSemanticSampler.call_semChal c
  have hsampler := AspisR1.UnifiedPayloadValue.sampler_payload_value
    SelectedTranscriptParams.params (by norm_num [SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
      i hi0 (by omega) (LiteralTranscript.erasePrefix P) mm
  have hstep := AspisR1.UnifiedPayloadStep.payload_step
    SelectedTranscriptParams.params (by norm_num [SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
      i hi0 (by omega) (by omega) (LiteralTranscript.erasePrefix P) mm
  have hchallenge :
      Value.ordinary (sourceChallenge c) =
        Value.ordinary (SelectedTranscriptParams.params.σ i
          (Hbytes (squeezeA SelectedTranscriptParams.params
            (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
              (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes)) := by
    congr 1
    calc
      sourceChallenge c = R0P.SemSource.semChal (decodeState c.block) := hq
      _ = SelectedTranscriptParams.params.σ i
          (Hbytes (squeezeA SelectedTranscriptParams.params
            (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
              (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes) := by
        symm
        rw [SelectedTranscriptParams.params_sigma, SelectedChallengeMap.semantic_row i hi]
        rw [hblock]
  constructor
  · rw [LiteralTranscript.samp, hm]
    change Value.ordinary (sourceChallenge c) =
      (AspisV8R19.MemoizedProgramLaw.eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (UnifiedSampler.samp SelectedTranscriptParams.params
          (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
          i (LiteralTranscript.erasePrefix P) (.payload mm)).toProgram).2.1
    rw [hsampler]
    exact hchallenge
  · rw [LiteralTranscript.samp, hm]
    change decodeState c.after.state =
      (AspisV8R19.MemoizedProgramLaw.eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (UnifiedSampler.samp SelectedTranscriptParams.params
          (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
          i (LiteralTranscript.erasePrefix P) (.payload mm)).toProgram).2.2
    rw [hstep]
    exact hnext

#print axioms call_functional_from_log
#print axioms call_simulates_literal_payload
end AspisR1PublicPreparation.SourceGlobalOracleCoupling
end
