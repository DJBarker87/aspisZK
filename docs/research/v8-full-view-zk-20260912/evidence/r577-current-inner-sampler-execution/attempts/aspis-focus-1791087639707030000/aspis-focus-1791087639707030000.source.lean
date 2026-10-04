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

theorem current_roundtrip (t : NTranscript) :
    fromCurrentTranscript (toCurrentTranscript t) = t := by
  cases t
  rfl

theorem nativeSqueeze_execution (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s = (do
      let out ← s.hash (R147QuerySqueezeBridge.message s.state 1#u8)
      let next ← s.hash (R147QuerySqueezeBridge.message s.state 2#u8)
      ok (out, {s with state := next})) := by
  have hs : s.state.val.length = 32 := s.state.property
  have ht : s.state.val.take 32 = s.state.val := List.take_of_length_le (by omega)
  simp [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.repeat, Array.to_slice, Slice.length, Slice.len,
    core.slice.Slice.copy_from_slice, Array.from_slice, List.setSlice!,
    List.slice, Array.update,
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.DOM_SQUEEZE,
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.DOM_ADVANCE,
    R147QuerySqueezeBridge.message, R147QuerySqueezeBridge.frame,
    Array.make, lift, bind_tc_ok, hs, List.set_append, ht]

theorem nativeSqueeze_map (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s = (do
      let (b, t) ← AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block (toCurrentTranscript s)
      ok (b, fromCurrentTranscript t)) := by
  rw [nativeSqueeze_execution, R167TranscriptPrimitiveExecution.r156_execution]
  cases s with
  | mk state hash =>
    simp [toCurrentTranscript, fromCurrentTranscript, bind_assoc_eq, bind_tc_ok,
      Prod.fst, Prod.snd]


abbrev NativePending := (core.ops.range.Range U32) × NTranscript ×
  Array U8 32#usize × Usize
abbrev NativeFinished := NTranscript × Array U8 32#usize × Usize ×
  AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31 × Bool
abbrev CurrentPending := (core.ops.range.Range U32) × CTranscript ×
  Array U8 32#usize × Usize
abbrev CurrentFinished := CTranscript × Array U8 32#usize × Usize ×
  AspisR156FullFreeze.aspis_core.field.M31 × Bool

def pendingNative (x : CurrentPending) : NativePending :=
  (x.1, fromCurrentTranscript x.2.1, x.2.2.1, x.2.2.2)
def finishedNative (x : CurrentFinished) : NativeFinished :=
  (fromCurrentTranscript x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
def nativeControl (x : ControlFlow CurrentPending CurrentFinished) :
    ControlFlow NativePending NativeFinished :=
  match x with
  | .cont x => .cont (pendingNative x)
  | .done x => .done (finishedNative x)

theorem body_map (limb : AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31)
    (r : core.ops.range.Range U32) (s : NTranscript) (b : Array U8 32#usize)
    (j : Usize) (hj : j.val ≤ 8) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body
      limb r s b j = (do
        let v ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0.body limb r
          (toCurrentTranscript s) b j
        ok (nativeControl v)) := by
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
    bind_assoc_eq, bind_tc_ok, lift]
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
        | fail e =>
            have hn : AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s = .fail e := by
              rw [nativeSqueeze_map, hs]
              simp only [bind_tc_fail]
            rw [hn]
            simp only [bind_tc_fail]
        | div =>
            have hn : AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s = .div := by
              rw [nativeSqueeze_map, hs]
              simp only [bind_tc_div]
            rw [hn]
            simp only [bind_tc_div]
        | ok pair =>
          rcases pair with ⟨b1, s1⟩
          have hn : AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.squeeze_block s =
              .ok (b1, fromCurrentTranscript s1) := by
            rw [nativeSqueeze_map, hs]
            simp only [bind_tc_ok]
          rw [hn]
          simp only [bind_assoc_eq, bind_tc_ok, nativeControl, pendingNative, finishedNative]
          have h0 : (0#usize : Usize).val ≤ 8 := by decide
          have hm0 := hmul 0#usize h0
          have ha0 := hadd (Std.Usize.wrapping_mul 0#usize 4#usize) (by simp [Std.Usize.wrapping_mul])
          have hn0 := hone 0#usize h0
          simp only [hm0, ha0, hn0, bind_assoc_eq, bind_tc_ok,
            nativeControl, pendingNative, finishedNative]
          congr 1
          funext slice
          congr 1
          funext raw
          congr 1
          funext bytes
          split <;> rfl
      · have hj : j.val < 8 := by
          have hne : j.val ≠ 8 := by
            intro hval
            apply hr
            exact UScalar.eq_of_val_eq hval
          omega
        simp only [if_neg hr, bind_assoc_eq]
        have hmj := hmul j (by omega)
        have hjmul : (Std.Usize.wrapping_mul j 4#usize).val ≤ 28 := by
          have hmval : Std.Usize.wrapping_mul j 4#usize = SamplerWordRead.small (j.val * 4) (by omega) := by
            have hcheck : (j * 4#usize : Result Usize) = .ok (SamplerWordRead.small (j.val * 4) (by omega)) := by
              change UScalar.tryMk .Usize (j.val * 4) = _
              exact SamplerWordRead.try_small _ (by omega)
            have heq : Result.ok (Std.Usize.wrapping_mul j 4#usize) =
                .ok (SamplerWordRead.small (j.val * 4) (by omega)) := by
              rw [← hmj, hcheck]
            injection heq
          rw [hmval]
          change j.val * 4 ≤ 28
          omega
        have haj := hadd (Std.Usize.wrapping_mul j 4#usize) hjmul
        have hnj := hone j (by omega)
        simp only [hmj, haj, hnj, bind_assoc_eq, bind_tc_ok,
          nativeControl, pendingNative, finishedNative]
        congr 1
        funext slice
        congr 1
        funext raw
        congr 1
        funext bytes
        split <;> rfl
end AspisV8R19.R577NativeInnerSamplerExecution
