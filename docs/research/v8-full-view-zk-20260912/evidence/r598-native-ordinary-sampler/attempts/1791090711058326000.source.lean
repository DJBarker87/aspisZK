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

def nativeOutcome (r : Result CQM31 Unit) : Result NQM31 Unit :=
  match r with
  | .ok q => .ok (nativeQM31 q)
  | .fail e => .fail e
  | .div => .div

abbrev NFinished := NTranscript × Option (Result NQM31 Unit) × NIter
abbrev CFinished := CTranscript × Option (Result CQM31 Unit) × CIter
abbrev NPending := NIter × (NIter → NIter) × NTranscript × Array U8 32#usize × Usize
abbrev CPending := CIter × (CIter → CIter) × CTranscript × Array U8 32#usize × Usize

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
  cases hs : AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0
      r sourceState b j limb with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok out =>
      rcases out with ⟨sr, br, jr, vr, accepted⟩
      simp only [hs, bind_tc_ok, AspisV8R19.R169InnerSamplerExecution.finished] at h
      have hinv := AspisV8R19.R137SamplerInnerLoop.source_result_invariant
        8 {start := 0#u32, «end» := 8#u32} sourceState sr br j jr limb vr accepted
        hj (by rfl) hs
      cases h
      exact hinv.1

end AspisV8R19.R598NativeOrdinarySampler
