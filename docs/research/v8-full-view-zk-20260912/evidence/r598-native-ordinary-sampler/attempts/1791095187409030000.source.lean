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

theorem toCurrent_fromCurrent (s : CTranscript) :
    toCurrentTranscript (fromCurrentTranscript s) = s := by
  cases s
  rfl

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
      | fail e =>
          have hc' : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
              {start := 0#u32,
                «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
              (R577NativeInnerSamplerExecution.toCurrentTranscript s) b j
              (it.slice[it.i]) = .fail e := by
            simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
              toCurrentTranscript] using hc
          simp only [hc', bind_tc_fail]
      | div =>
          have hc' : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
              {start := 0#u32,
                «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
              (R577NativeInnerSamplerExecution.toCurrentTranscript s) b j
              (it.slice[it.i]) = .div := by
            simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
              toCurrentTranscript] using hc
          simp only [hc', bind_tc_div]
      | ok out =>
          rcases out with ⟨s1, b1, j1, value, accepted⟩
          cases accepted with
          | false =>
              have hc' : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
                  {start := 0#u32,
                    «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
                  (R577NativeInnerSamplerExecution.toCurrentTranscript s) b j
                  (it.slice[it.i]) = .ok (s1, b1, j1, value, false) := by
                simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
                  toCurrentTranscript] using hc
              rw [hc']
              simp [bind_tc_ok, finishedNativeOuter, fromCurrentTranscript,
                R577NativeInnerSamplerExecution.finishedNative,
                R577NativeInnerSamplerExecution.fromCurrentTranscript,
                R577NativeInnerSamplerExecution.toCurrentTranscript,
                toCurrentTranscript, nativeOutcome]
          | true =>
              have hc' : AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0_loop0
                  {start := 0#u32,
                    «end» := AspisR156FullFreeze.aspis_core.transcript.CHALLENGE_RETRY_LIMIT}
                  (R577NativeInnerSamplerExecution.toCurrentTranscript s) b j
                  (it.slice[it.i]) = .ok (s1, b1, j1, value, true) := by
                simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
                  toCurrentTranscript] using hc
              rw [hc']
              have hj' := currentInner_accepted_index_bound (toCurrentTranscript s)
                b j (it.slice[it.i]) value s1 b1 j1 hj hc
              simp only [bind_tc_ok, finishedNativeOuter,
                R577NativeInnerSamplerExecution.finishedNative,
                R577NativeInnerSamplerExecution.fromCurrentTranscript,
                R577NativeInnerSamplerExecution.toCurrentTranscript, if_true]
              simpa only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0,
                AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0,
                AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
                AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31_loop0.body,
                core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok,
                finishedNativeOuter, toCurrentTranscript, fromCurrentTranscript,
                toCurrent_fromCurrent] using
                ih {it with i := it.i + 1}
                  (fun out => back {out with slice := out.slice.setAtNat it.i value})
                  (fromCurrentTranscript s1) b1 j1 hj' hn'

def nativeInitial : Array AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31 4#usize :=
  Array.repeat 4#usize AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31.ZERO

def nativeInitialIter : NIter :=
  { slice := (Array.repeat 4#usize
      AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31.ZERO).to_slice }

def nativeFinishChallenge (x : NFinished) :
    Aeneas.Std.Result ((core.result.Result NQM31
      AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.ChallengeSampleExhausted) ×
      NTranscript) :=
  let (s, pending, it) := x
  match pending with
  | none => do
      let limbs := Array.from_slice nativeInitial it.slice
      let m ← Array.index_usize limbs 0#usize
      let m1 ← Array.index_usize limbs 1#usize
      let m2 ← Array.index_usize limbs 2#usize
      let m3 ← Array.index_usize limbs 3#usize
      ok (core.result.Result.Ok
        { c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } }, s)
  | some r => ok (r, s)

theorem nativeInitial_len : nativeInitialIter.slice.len - nativeInitialIter.i = 4 := by
  rfl

theorem pair_bind_nested {X : Type} (b : Array U8 32#usize)
    (s1 : AspisR156FullFreeze.aspis_core.transcript.Transcript)
    (k : Array U8 32#usize × NTranscript → Aeneas.Std.Result X) :
    (do
      let x ← (ok (b, s1) : Aeneas.Std.Result
        (Array U8 32#usize × AspisR156FullFreeze.aspis_core.transcript.Transcript))
      let p ← (let (b', t') := x
        ok (b', R577NativeInnerSamplerExecution.fromCurrentTranscript t'))
      k p) = k (b, R577NativeInnerSamplerExecution.fromCurrentTranscript s1) := rfl

def returnedChallenge (x : core.result.Result CQM31 Unit × CTranscript) :
    core.result.Result NQM31 Unit × NTranscript :=
  (nativeOutcome x.1, fromCurrentTranscript x.2)

theorem pair_bind {X : Type} (b : Array U8 32#usize)
    (s1 : AspisR156FullFreeze.aspis_core.transcript.Transcript)
    (k : Array U8 32#usize × NTranscript → Aeneas.Std.Result X) :
    (do
      let p ← (let (b', t') := (b, s1)
        ok (b', R577NativeInnerSamplerExecution.fromCurrentTranscript t'))
      k p) = k (b, R577NativeInnerSamplerExecution.fromCurrentTranscript s1) := rfl

theorem challenge_map (s : NTranscript) :
    AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31 s = (do
      let v ← AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31
        (toCurrentTranscript s)
      ok (returnedChallenge v)) := by
  simp only [AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31,
    AspisR156FullFreeze.aspis_core.transcript.Transcript.challenge_qm31,
    R577NativeInnerSamplerExecution.nativeSqueeze_map,
    bind_assoc_eq, lift, bind_tc_ok,
    AspisR569MaskedClaimCompleteConsts.aspis_core.field.M31.ZERO,
    AspisR156FullFreeze.aspis_core.field.M31.ZERO]
  generalize hlimbs : (Array.repeat 4#usize 0#u32) = limbs
  with_unfolding_all simp only [Array.to_slice_mut, core.slice.Slice.iter_mut,
    lift, bind_tc_ok]
  cases hs : AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block
      (R577NativeInnerSamplerExecution.toCurrentTranscript s) with
  | fail e =>
      have hs' : AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block
          (toCurrentTranscript s) = .fail e := by
        simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
          toCurrentTranscript] using hs
      simp only [hs', bind_tc_fail]
  | div =>
      have hs' : AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block
          (toCurrentTranscript s) = .div := by
        simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
          toCurrentTranscript] using hs
      simp only [hs', bind_tc_div]
  | ok pair =>
      rcases pair with ⟨b, s1⟩
      have hs' : AspisR156FullFreeze.aspis_core.transcript.Transcript.squeeze_block
          (toCurrentTranscript s) = .ok (b, s1) := by
        simpa [R577NativeInnerSamplerExecution.toCurrentTranscript,
          toCurrentTranscript] using hs
      with_unfolding_all simp only [hs', bind_tc_ok, Prod.fst, Prod.snd]
      change (do
        let out ← AspisR569MaskedClaimCompleteConsts.aspis_core.transcript.Transcript.challenge_qm31_loop0
          nativeInitialIter (fun it => it)
          (R577NativeInnerSamplerExecution.fromCurrentTranscript s1) b 0#usize
        nativeFinishChallenge out) = _
      rw [outer_loop_map 4 nativeInitialIter (fun it => it)
        (R577NativeInnerSamplerExecution.fromCurrentTranscript s1)
        b 0#usize (by decide) nativeInitial_len]
      simp only [bind_assoc_eq, bind_tc_ok]
      congr 1
      funext x
      rcases x with ⟨s2, pending, iter⟩
      simp only [finishedNativeOuter]
      cases pending with
      | some r => rfl
      | none =>
          simp only [returnedChallenge, Option.map_none, nativeOutcome,
            fromCurrentTranscript, toCurrent_fromCurrent, bind_assoc_eq]
          congr 1


end AspisV8R19.R598NativeOrdinarySampler
