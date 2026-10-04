import AspisV8R19.R598NativeOrdinarySampler
import AspisV8R19.R173NonzeroExecution
import AspisV8R19.SamplerOuterExecution

set_option autoImplicit false
namespace AspisV8R19.R613NativeNonzeroExecution
open Aeneas Aeneas.Std Result ControlFlow

abbrev NTranscript := AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript
abbrev CTranscript := AspisR156FullFreeze.aspis_core.transcript.Transcript
abbrev NQM31 := AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31
abbrev CQM31 := AspisR156FullFreeze.aspis_core.field.QM31
abbrev NExhausted := AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.ChallengeSampleExhausted
abbrev CExhausted := AspisR156FullFreeze.aspis_core.transcript.ChallengeSampleExhausted
abbrev Range := core.ops.range.Range U32
abbrev NResult := core.result.Result NQM31 NExhausted
abbrev CResult := core.result.Result CQM31 CExhausted

open AspisR156FullFreeze.aspis_core

/-- Convert the successful field value while preserving the native error and state. -/
def returned (x : CResult × CTranscript) : NResult × NTranscript :=
  (match x.1 with
   | .Ok q => .Ok AspisV8R19.R598NativeOrdinarySampler.nativeQM31 q
   | .Err e => .Err e,
   AspisV8R19.R598NativeOrdinarySampler.fromCurrentTranscript x.2)

def mapPending (x : Range × CTranscript) : Range × NTranscript :=
  (x.1, AspisV8R19.R598NativeOrdinarySampler.fromCurrentTranscript x.2)

def mapControl (x : ControlFlow (Range × CTranscript) (CResult × CTranscript)) :
    ControlFlow (Range × NTranscript) (NResult × NTranscript) :=
  match x with
  | .cont p => .cont (mapPending p)
  | .done r => .done (returned r)

theorem ne_map (q : CQM31) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.cmp.PartialEq.ne.trait_default
      AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (AspisV8R19.R598NativeOrdinarySampler.nativeQM31 q)
      AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31.ZERO =
    core.cmp.PartialEq.ne.trait_default
      AspisR156FullFreeze.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      q AspisR156FullFreeze.aspis_core.field.QM31.ZERO := by
  simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR156FullFreeze.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR156FullFreeze.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    AspisR156FullFreeze.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31.ZERO,
    AspisR156FullFreeze.aspis_core.field.QM31.ZERO,
    AspisV8R19.R598NativeOrdinarySampler.nativeQM31,
    bind_tc_ok]

theorem body_map (r : Range) (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body r s = (do
      let x ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body
        r (AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript s)
      ok (mapControl x)) := by
  simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
    SamplerOuterExecution.range_next, bind_assoc_eq, lift, bind_tc_ok,
    AspisV8R19.R598NativeOrdinarySampler.challenge_map]
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepU32 r with
  | fail e => simp [hn]
  | div => simp [hn]
  | ok pair =>
      rcases pair with ⟨o, r1⟩
      cases o with
      | none => simp [hn, returned, mapControl]
      | some _ =>
          simp only [hn, bind_tc_ok]
          cases hs : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31
              (AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript s) with
          | fail e => simp [hs]
          | div => simp [hs]
          | ok pair =>
              rcases pair with ⟨res, s1⟩
              cases res with
              | Err e => simp [hs, returned, mapControl]
              | Ok q =>
                  simp only [hs, bind_tc_ok, returned, mapControl,
                    AspisV8R19.R598NativeOrdinarySampler.nativeOutcome,
                    ne_map]
                  cases hz : core.cmp.PartialEq.ne.trait_default
                      AspisR156FullFreeze.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
                      AspisR156FullFreeze.aspis_core.field.QM31.ZERO with
                  | fail e => simp [hz]
                  | div => simp [hz]
                  | ok nz => cases nz <;> simp [hz, mapControl, mapPending, returned]

theorem loop_map (n : Nat) (r : Range) (s : NTranscript)
    (hn : r.end.val - r.start.val = n) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop r s = (do
      let x ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop
        r (AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript s)
      ok (returned x)) := by
  induction n generalizing r s with
  | zero =>
      have h : ¬ r.start.val < r.end.val := by omega
      rw [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
        loop.eq_def]
      simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
        SamplerOuterExecution.range_next, dif_neg h, bind_tc_ok]
      rw [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
        loop.eq_def]
      simp only [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
        SamplerOuterExecution.range_next, dif_neg h, bind_tc_ok, returned]
      rfl
  | succ n ih =>
      have h : r.start.val < r.end.val := by omega
      let r' : Range :=
        { start := UScalar.ofNatCore (r.start.val + 1)
            (by have := r.end.hBounds; omega), «end» := r.end }
      have hn' : r'.end.val - r'.start.val = n := by
        change r.end.val - (r.start.val + 1) = n
        omega
      rw [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
        loop.eq_def]
      simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
        SamplerOuterExecution.range_next, dif_pos h, bind_tc_ok]
      rw [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
        loop.eq_def]
      simp only [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
        SamplerOuterExecution.range_next, dif_pos h, bind_tc_ok]
      cases hs : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31
          (AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript s) with
      | fail e => simp [hs]
      | div => simp [hs]
      | ok pair =>
          rcases pair with ⟨res, s1⟩
          cases res with
          | Err e => simp [hs, returned]
          | Ok q =>
              simp only [hs, bind_tc_ok, ne_map]
              cases hz : core.cmp.PartialEq.ne.trait_default
                  AspisR156FullFreeze.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 q
                  AspisR156FullFreeze.aspis_core.field.QM31.ZERO with
              | fail e => simp [hz]
              | div => simp [hz]
              | ok nz =>
                  cases nz with
                  | true => simp [hz, returned]
                  | false =>
                      simp only [hz, Bool.false_eq_true, if_false, bind_tc_ok]
                      simpa only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
                        AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
                        AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop,
                        AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31_loop.body,
                        SamplerOuterExecution.range_next, bind_tc_ok, r'] using ih r' s1 hn'

theorem challenge_map (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31 s = (do
      let x ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31
        (AspisV8R19.R598NativeOrdinarySampler.toCurrentTranscript s)
      ok (returned x)) := by
  simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_nonzero_qm31,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_nonzero_qm31,
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.NONZERO_QM31_RETRY_LIMIT,
    AspisR156FullFreeze.aspis_core.transcript.NONZERO_QM31_RETRY_LIMIT]
  rw [loop_map 3 _ _ (by rfl)]

#print axioms returned
#print axioms mapPending
#print axioms mapControl
#print axioms ne_map
#print axioms body_map
#print axioms loop_map
#print axioms challenge_map
end AspisV8R19.R613NativeNonzeroExecution
