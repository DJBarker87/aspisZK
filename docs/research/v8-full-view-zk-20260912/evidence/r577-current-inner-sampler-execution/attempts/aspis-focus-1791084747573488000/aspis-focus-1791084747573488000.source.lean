import AspisV8R19.R575NativeClaimHashCall
import AspisV8R19.R169InnerSamplerExecution
import AspisV8R19.R137SamplerWordRead
import AspisV8R19.R137SamplerInnerLoop

set_option autoImplicit false
namespace AspisV8R19.R577NativeInnerSamplerExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.R575NativeClaimHashCall

abbrev NTranscript := AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript
abbrev CTranscript := AspisR156FullFreeze.aspis_core.transcript.Transcript
abbrev RTranscript := AspisR137Transcript.transcript.Transcript

 def toCurrentTranscript (t : NTranscript) : CTranscript := ⟨t.state, t.hash⟩
 def fromCurrentTranscript (t : CTranscript) : NTranscript := ⟨t.state, t.hash⟩

def toR137Transcript (t : RTranscript) : AspisR137Transcript.transcript.Transcript := t

def nativeSqueeze_map (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s = (do
      let (b, t) ← AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block (toCurrentTranscript s)
      ok (b, fromCurrentTranscript t)) := by
  rw [R167TranscriptPrimitiveExecution.r156_execution (toCurrentTranscript s)]
  cases s with
  | mk state hash =>
    simp [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block,
      toCurrentTranscript, fromCurrentTranscript,
      AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.DOM_SQUEEZE,
      AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.DOM_ADVANCE,
      AspisR156FullFreeze.aspis_core.transcript.DOM_SQUEEZE,
      AspisR156FullFreeze.aspis_core.transcript.DOM_ADVANCE,
      R147QuerySqueezeBridge.message, R147QuerySqueezeBridge.frame]


abbrev NativePending := (core.ops.range.Range U32) × NTranscript ×
  Array U8 32#usize × Usize
abbrev NativeFinished := NTranscript × Array U8 32#usize × Usize ×
  AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31 × Bool
abbrev CurrentPending := (core.ops.range.Range U32) × CTranscript ×
  Array U8 32#usize × Usize
abbrev CurrentFinished := CTranscript × Array U8 32#usize × Usize ×
  AspisR156FullFreeze.aspis_core.field.M31 × Bool

def pendingCurrent (x : NativePending) : CurrentPending :=
  (x.1, toCurrentTranscript x.2.1, x.2.2.1, x.2.2.2)
def finishedCurrent (x : NativeFinished) : CurrentFinished :=
  (toCurrentTranscript x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
def currentControl (x : ControlFlow NativePending NativeFinished) :
    ControlFlow CurrentPending CurrentFinished :=
  match x with
  | .cont x => .cont (pendingCurrent x)
  | .done x => .done (finishedCurrent x)

theorem body_map (limb : AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31)
    (r : core.ops.range.Range U32) (s : NTranscript) (b : Array U8 32#usize)
    (j : Usize) (hj : j.val ≤ 8) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
      limb r s b j = (do
        let v ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body limb r
          (toCurrentTranscript s) b j
        ok (currentControl v)) := by
  have hmul (x : Usize) (hx : x.val ≤ 8) :
      (x * 4#usize : Result Usize) = .ok (Std.Usize.wrapping_mul x 4#usize) := by
    have h := R137SamplerWordRead.wrapping_mul_checked x hx
    simpa only [lift] using h.symm
  have hadd (x : Usize) (hx : x.val ≤ 28) :
      (x + 4#usize : Result Usize) = .ok (Std.Usize.wrapping_add x 4#usize) := by
    have h := R137SamplerWordRead.wrapping_add_four_checked x hx
    simpa only [lift] using h.symm
  have hone (x : Usize) (hx : x.val ≤ 8) :
      (x + 1#usize : Result Usize) = .ok (Std.Usize.wrapping_add x 1#usize) := by
    have h := R137SamplerWordRead.wrapping_add_one_checked x hx
    simpa only [lift] using h.symm
  simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.P,
    AspisR156FullFreeze.aspis_core.field.P,
    nativeSqueeze_map, bind_assoc_eq, bind_tc_ok, lift]
  cases hi : core.iter.range.IteratorRange.next core.iter.range.StepU32 r with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨o, r1⟩
    cases o with
    | none => rfl
    | some v =>
      by_cases hr : j = 8#usize
      · simp only [if_pos hr, bind_assoc_eq, bind_tc_ok]
        cases hs : AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block (toCurrentTranscript s) with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨b1, s1⟩
          simp only [hs, bind_tc_ok, currentControl, pendingCurrent, finishedCurrent]
          have h0 : (0#usize : Usize).val ≤ 8 := by decide
          have hm0 := hmul 0#usize h0
          have ha0 := hadd (Std.Usize.wrapping_mul 0#usize 4#usize) (by simp [Std.Usize.wrapping_mul])
          have hn0 := hone 0#usize h0
          simp only [hm0, ha0, hn0, bind_tc_ok]
          rfl
      · have hj : j.val < 8 := by
          have hv := j.val
          have heq : (8#usize : Usize).val = 8 := rfl
          have := congrArg UScalar.val hr
          simp at this
          omega
        simp only [if_neg hr, bind_assoc_eq, bind_tc_ok]
        have hmj := hmul j (by omega)
        have hjmul : (Std.Usize.wrapping_mul j 4#usize).val ≤ 28 := by
          have hmval : Std.Usize.wrapping_mul j 4#usize = small (j.val * 4) (by omega) := by
            have hcheck : (j * 4#usize : Result Usize) = .ok (small (j.val * 4) (by omega)) := by
              change UScalar.tryMk .Usize (j.val * 4) = _
              exact SamplerWordRead.try_small _ (by omega)
            have := hmj.symm.trans hcheck
            exact (Result.ok.inj this)
          rw [hmval]
          simp only [SamplerWordRead.small_val]
          omega
        have haj := hadd (Std.Usize.wrapping_mul j 4#usize) hjmul
        have hn j := hone j (by omega)
        simp only [hmj, haj, hn j, bind_tc_ok]
        rfl

end AspisV8R19.R577NativeInnerSamplerExecution
