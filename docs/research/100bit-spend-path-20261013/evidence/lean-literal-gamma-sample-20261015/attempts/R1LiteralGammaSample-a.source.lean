import R1LiteralByteSampler
import R1LiteralSemanticMessageFacts
import R1UnifiedSamplerLaw
import R1SelectedOpeningEventMass

/-! A valid literal row-27 message samples the selected nonzero gamma.
This is an all-byte sampler fact; it makes no source or acceptance claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralGammaSample

open FS FS2 FS2.Duplex
open AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleProgramOps AspisV8R19.MemoizedProgramLaw
open AspisV8R19.DuplexFrames
open AspisR1.TranscriptView

theorem valid_row27_nonzero
    (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message)
    (hm : LiteralTranscript.valid 27 m) :
    ∃ gamma state,
      (eval H (LiteralByteSampler.samp 27 P m).toProgram).2 =
        (Value.ordinary gamma, state) ∧ gamma ≠ 0 := by
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hm
  | c2 bytes word => simp [LiteralTranscript.valid] at hm
  | second bytes word => simp [LiteralTranscript.valid] at hm
  | payload bytes =>
      let p := SelectedTranscriptParams.params
      let P' := LiteralTranscript.erasePrefix P
      let msg : SelectedTranscriptParams.Message := bytes
      let addr := UnifiedSampler.absorb p 27 P' msg
      let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State :=
        fun a => H a.toBytes
      let squeezed := H' (squeezeA p (H' addr))
      let advanced := H' (advanceA p (H' addr))
      have hD : 5 ≤ p.D := by
        norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
      have hrow : UnifiedSampler.samp p hD 27 P' (.payload msg) =
          DuplexSamplers.plain p addr 27 liftChallenge :=
        UnifiedSampler.row_ordinary p hD 27 (by omega) (by omega) (by omega) P' msg
      have hselected :
          (eval H' (LiteralTranscript.samp 27 P (.payload bytes)).toProgram).2 =
            liftChallenge (p.σ 27 squeezed, advanced) := by
        rw [LiteralTranscript.samp, hrow]
        simpa [addr, squeezed, advanced] using
          (congrArg Prod.snd (DuplexSamplers.plain_eval p addr 27 liftChallenge H'))
      have hmap := congrArg Prod.snd
        (LiteralByteSampler.eval_eq H 27 P (.payload bytes))
      have hresult :
          (eval H (LiteralByteSampler.samp 27 P (.payload bytes)).toProgram).2 =
            liftChallenge (p.σ 27 squeezed, advanced) := by
        calc
          _ = (OracleProgramOps.mapView FS2.Duplex.Addr.toBytes
                (eval H' (LiteralTranscript.samp 27 P (.payload bytes)).toProgram)).2 := hmap
          _ = (eval H' (LiteralTranscript.samp 27 P (.payload bytes)).toProgram).2 := by
                simp [OracleProgramOps.mapView]
          _ = _ := hselected
      refine ⟨SelectedChallengeMap.sigma 27 squeezed, advanced, ?_, ?_⟩
      · simpa [SelectedTranscriptParams.params_sigma, liftChallenge] using hresult
      · exact SelectedOpeningEventMass.gamma_ne_zero squeezed

#print axioms valid_row27_nonzero

end AspisR1.LiteralGammaSample
end
