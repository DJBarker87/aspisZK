import RPz7_ExtractedSourceSemanticSampler
import RPz7_ExtractedSourceDigestOracle
import R1UnifiedPayloadStep
import R1UnifiedPayloadValue
import R1LiteralTranscript
import R1SelectedTranscriptParams

set_option autoImplicit false
noncomputable section

namespace AspisR1PublicPreparation.SourceLiteralSamplerStep

open Aeneas Aeneas.Std Result
open AspisR1
open AspisR1.TranscriptView
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisR1.LiteralTranscript
open AspisR1.SelectedTranscriptParams
open AspisV8R15.ExactTowerBase AspisV8R19.R599CanonicalFieldTuple

private abbrev sourceChallenge {H : Type} {D : aspis_core.Digest32 H}
    {pre : r1_wire.Prefix} (c : SourceFull25.Call D pre) : AspisWideTower.WideExact :=
  algebraMap QM31Exact AspisWideTower.WideExact
    (ExtractedCurrentQM31Exact.decode
      (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld c.q)))

/-- A reached source call simulates the literal payload sampler when their
prior state and framed payload agree. The source digest equations are obtained
from the actual trace's functional-oracle theorem, not postulated per call. -/
theorem call_simulates_literal_payload
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (c : SourceFull25.Call D pre) (hc : c ∈ cs)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (Hbytes : Bytes → State)
    (horacle : ∀ a : Addr SelectedTranscriptParams.L,
      SourceDigestOracle.oracle D before.hash pubInput root length a = Hbytes a.toBytes)
    (hD : ∀ d ∈ cs, (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.D)
    (i : Nat) (hi : i < 25) (hi0 : i ≠ 0)
    (hrow : c.row.val = i)
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
  have htrace := SourceDigestOracle.trace_functional SelectedTranscriptParams.params
    run pubInput root length hD c hc
  have habsVal : decodeState c.absorbed =
      Hbytes (absorbA SelectedTranscriptParams.params
        (decodeState c.before.state) (decodeByte c.tag)
        (rawBytes c.record.framed) hbound).toBytes := by
    calc
      decodeState c.absorbed = SourceDigestOracle.oracle D before.hash pubInput root length
          (absorbA SelectedTranscriptParams.params (decodeState c.before.state)
            (decodeByte c.tag) (rawBytes c.record.framed) (hD c hc)) := htrace.1
      _ = Hbytes (absorbA SelectedTranscriptParams.params
          (decodeState c.before.state) (decodeByte c.tag)
          (rawBytes c.record.framed) hbound).toBytes := by
        rw [horacle]
  have hblock : decodeState c.block =
      Hbytes (squeezeA SelectedTranscriptParams.params
        (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
          (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes := by
    calc
      decodeState c.block = SourceDigestOracle.oracle D before.hash pubInput root length
          (squeezeA SelectedTranscriptParams.params (decodeState c.absorbed)) := htrace.2.1
      _ = Hbytes (squeezeA SelectedTranscriptParams.params
          (decodeState c.absorbed)).toBytes := horacle _
      _ = _ := by rw [habsVal, habsorb]
  have hnext : decodeState c.after.state =
      Hbytes (advanceA SelectedTranscriptParams.params
        (Hbytes (UnifiedSampler.absorb SelectedTranscriptParams.params i
          (LiteralTranscript.erasePrefix P) mm).toBytes)).toBytes := by
    calc
      decodeState c.after.state = SourceDigestOracle.oracle D before.hash pubInput root length
          (advanceA SelectedTranscriptParams.params (decodeState c.absorbed)) := htrace.2.2
      _ = Hbytes (advanceA SelectedTranscriptParams.params
          (decodeState c.absorbed)).toBytes := horacle _
      _ = _ := by rw [habsVal, habsorb]
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

#print axioms call_simulates_literal_payload

end AspisR1PublicPreparation.SourceLiteralSamplerStep
end
