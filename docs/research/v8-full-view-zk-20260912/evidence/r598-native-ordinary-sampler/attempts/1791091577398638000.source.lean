import AspisV8R19.R577NativeInnerSamplerExecution
import AspisV8R19.R169InnerSamplerExecution
import AspisV8R19.R137SamplerInnerLoop
import AspisV8R19.R167TranscriptPrimitiveExecution

set_option autoImplicit false
namespace AspisV8R19.R598NativeOrdinarySampler
open Aeneas Aeneas.Std Result ControlFlow

abbrev NTranscript := AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript
abbrev CTranscript := AspisR156FullFreeze.aspis_core.transcript.Transcript
abbrev NQM31 := AspisR569MaskedClaimCompleteConsts.aspis_core.field.QM31
abbrev CQM31 := AspisR156FullFreeze.aspis_core.field.QM31
abbrev NIter := core.slice.iter.IterMut AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31
abbrev CIter := core.slice.iter.IterMut AspisR156FullFreeze.aspis_core.field.M31

def toCurrentTranscript (s : NTranscript) : CTranscript := ⟨s.state, s.hash⟩
def fromCurrentTranscript (s : CTranscript) : NTranscript := ⟨s.state, s.hash⟩

def nativeQM31 (q : CQM31) : NQM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def nativeOutcome (r : core.result.Result CQM31 Unit) : core.result.Result NQM31 Unit :=
  match r with
  | .Ok q => .Ok (nativeQM31 q)
  | .Err e => .Err e

abbrev NFinished := NTranscript × Option (core.result.Result NQM31 Unit) × NIter
abbrev CFinished := CTranscript × Option (core.result.Result CQM31 Unit) × CIter
abbrev NPending := NIter × (NIter → NIter) × NTranscript × Array U8 32#usize × Usize
abbrev CPending := CIter × (CIter → CIter) × CTranscript × Array U8 32#usize × Usize

def nativeOuterBody (it : NIter) (back : NIter → NIter) (s : NTranscript)
    (b : Array U8 32#usize) (j : Usize) :=
  AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
    it back s b j

def currentOuterBody (it : CIter) (back : CIter → CIter) (s : CTranscript)
    (b : Array U8 32#usize) (j : Usize) :=
  AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0.body
    it back s b j

def finishedNativeOuter (x : CFinished) : NFinished :=
  (fromCurrentTranscript x.1, x.2.1.map nativeOutcome, x.2.2)

def pendingNativeOuter (x : CPending) : NPending :=
  (x.1, x.2.1, fromCurrentTranscript x.2.2.1, x.2.2.2.1, x.2.2.2.2)

def nativeControlOuter (x : ControlFlow CPending CFinished) :
    ControlFlow NPending NFinished :=
  match x with
  | .cont p => .cont (pendingNativeOuter p)
  | .done f => .done (finishedNativeOuter f)

theorem outer_loop_map (n : Nat) (it : NIter) (back : NIter → NIter)
    (s : NTranscript) (b : Array U8 32#usize) (j : Usize)
    (hj : j.val ≤ 8) (hn : it.slice.len - it.i = n) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0
      it back s b j = (do
        let v ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0
          it back (toCurrentTranscript s) b j
        ok (finishedNativeOuter v)) := by
  induction n generalizing it back s b j with
  | zero =>
      have h : ¬ it.i < it.slice.len := by omega
      rw [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_neg h, bind_tc_ok]
      rw [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_neg h, bind_tc_ok]
      simp [finishedNativeOuter, fromCurrentTranscript, toCurrentTranscript]
      cases s <;> rfl
  | succ n ih =>
      have h : it.i < it.slice.len := by omega
      have hn' : it.slice.len - (it.i + 1) = n := by omega
      rw [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok]
      rw [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok]
      simp only [AspisV8R19.R577NativeInnerSamplerExecution.eight_attempts_map
        s b j it.slice[it.i] hj]
      cases hc : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
          {start := 0#u32,
            «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
          (toCurrentTranscript s) b j (it.slice[it.i]) with
      | fail e => simp [hc]
      | div => simp [hc]
      | ok out =>
          rcases out with ⟨s1, b1, j1, value, accepted⟩
          cases accepted with
          | false => simp [hc, finishedNativeOuter, fromCurrentTranscript]
          | true =>
              have hj' := currentInner_accepted_index_bound s b j (it.slice[it.i])
                s1 b1 j1 value hj hc
              simp only [bind_tc_ok, finishedNativeOuter]
              simpa only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0,
                AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0,
                AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
                AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
                core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok,
                toCurrentTranscript, fromCurrentTranscript] using
                ih {it with i := it.i + 1}
                  (fun out => back {out with slice := out.slice.setAtNat it.i value})
                  (fromCurrentTranscript s1) b1 j1 hj' hn'

theorem currentInner_accepted_index_bound (s : CTranscript)
    (b : Array U8 32#usize) (j : Usize)
    (limb value : AspisR156FullFreeze.aspis_core.field.M31)
    (s1 : CTranscript) (b1 : Array U8 32#usize) (j1 : Usize)
    (hj : j.val ≤ 8)
    (h : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
      {start := 0#u32,
        «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
      s b j limb = .ok (s1, b1, j1, value, true)) :
    j1.val ≤ 8 := by
  let sourceState := AspisV8R19.R167TranscriptPrimitiveExecution.toR137 s
  have hround : AspisV8R19.R167TranscriptPrimitiveExecution.fromR137 sourceState = s :=
    AspisV8R19.R167TranscriptPrimitiveExecution.from_to s
  rw [← hround] at h
  have hmap := AspisV8R19.R169InnerSamplerExecution.eight_attempts_map
    sourceState b j limb
  rw [hmap] at h
  let r : core.ops.range.Range U32 :=
    {start := 0#u32,
      «end» := AspisR137Transcript.transcript.CHALLENGE_RETRY_LIMIT}
  cases hs : AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0
      r sourceState b j limb with
  | fail e => rw [hs] at h; simp only [bind_tc_fail] at h; cases h
  | div => rw [hs] at h; simp only [bind_tc_div] at h; cases h
  | ok out =>
      rcases out with ⟨sr, br, jr, vr, accepted⟩
      rw [hs] at h
      simp only [bind_tc_ok, AspisV8R19.R169InnerSamplerExecution.finished] at h
      have hn : r.end.val - r.start.val = 8 := by
        norm_num [r, AspisR137Transcript.transcript.CHALLENGE_RETRY_LIMIT]
      have hinv := AspisV8R19.R137SamplerInnerLoop.source_result_invariant
        8 r
        sourceState sr b br j jr limb vr accepted hj hn hs
      have htuple : (AspisV8R19.R167TranscriptPrimitiveExecution.fromR137 sr,
          br, jr, vr, accepted) = (s1, b1, j1, value, true) := by
        injection h with heq
      have hjEq : jr = j1 := by
        cases htuple
        rfl
      simpa only [hjEq] using hinv.1

end AspisV8R19.R598NativeOrdinarySampler
