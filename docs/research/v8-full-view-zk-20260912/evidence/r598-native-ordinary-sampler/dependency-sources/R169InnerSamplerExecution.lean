import AspisV8R19.R167TranscriptPrimitiveExecution
import AspisV8R19.R137SamplerInnerLoop

set_option autoImplicit false
namespace AspisV8R19.R169InnerSamplerExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisR156FullFreeze.aspis_core
open R167TranscriptPrimitiveExecution

abbrev Pending := (core.ops.range.Range U32) × transcript.Transcript ×
  Array U8 32#usize × Usize
abbrev Finished := transcript.Transcript × Array U8 32#usize × Usize × U32 × Bool

def pending (x : R137SamplerInnerStep.Pending) : Pending :=
  (x.1, fromR137 x.2.1, x.2.2.1, x.2.2.2)
def finished (x : R137SamplerInnerStep.Finished) : Finished :=
  (fromR137 x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2)
def control (x : ControlFlow R137SamplerInnerStep.Pending
    R137SamplerInnerStep.Finished) : ControlFlow Pending Finished :=
  match x with
  | .cont x => .cont (pending x)
  | .done x => .done (finished x)

theorem body_map (limb : U32) (r : core.ops.range.Range U32)
    (s : AspisR137Transcript.transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r (fromR137 s) b j =
      (do
        let v ← AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0.body
          limb r s b j
        ok (control v)) := by
  simp only [transcript.Transcript.challenge_qm31_loop0_loop0.body,
    AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0.body,
    field.P, AspisR137Transcript.field.P, squeeze_map, to_from,
    bind_assoc_eq, bind_tc_ok, lift]
  cases h : core.iter.range.IteratorRange.next core.iter.range.StepU32 r with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨o,r1⟩
    cases o with
    | none => rfl
    | some v =>
      by_cases hj : j = 8#usize
      · simp only [if_pos hj, bind_assoc_eq, bind_tc_ok]
        cases hs : AspisR137Transcript.transcript.Transcript.squeeze_block s with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨b1,s1⟩
          simp only [bind_assoc_eq, bind_tc_ok, control, pending, finished]
          congr 1
          funext slice
          congr 1
          funext raw
          congr 1
          funext bytes
          split <;> rfl
      · simp only [if_neg hj, bind_assoc_eq, bind_tc_ok, control, pending, finished]
        congr 1
        funext slice
        congr 1
        funext raw
        congr 1
        funext bytes
        split <;> rfl

theorem loop_map (n : Nat) (r : core.ops.range.Range U32)
    (s : AspisR137Transcript.transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (limb : U32)
    (hn : r.end.val - r.start.val = n) :
    transcript.Transcript.challenge_qm31_loop0_loop0 r (fromR137 s) b j limb =
      (do
        let v ← AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0
          r s b j limb
        ok (finished v)) := by
  induction n generalizing r s b j with
  | zero =>
      have hr : ¬ r.start.val < r.end.val := by omega
      rw [transcript.Transcript.challenge_qm31_loop0_loop0, loop.eq_def]
      simp only [body_map]
      simp only [R137SamplerInnerStep.exhausted limb r s b j hr,
        bind_tc_ok, control, finished]
      rw [AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0,
        loop.eq_def]
      simp only [R137SamplerInnerStep.exhausted limb r s b j hr,
        bind_tc_ok, finished]
  | succ n ih =>
      have hr : r.start.val < r.end.val := by omega
      have hn' : (R137SamplerInnerStep.nextRange r hr).end.val -
          (R137SamplerInnerStep.nextRange r hr).start.val = n := by
        change r.end.val - (r.start.val + 1) = n
        omega
      rw [transcript.Transcript.challenge_qm31_loop0_loop0, loop.eq_def]
      simp only [body_map]
      rw [AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0,
        loop.eq_def]
      simp only [R137SamplerInnerStep.factor, R137SamplerInnerStep.factored,
        SamplerOuterExecution.range_next, dif_pos hr, bind_tc_ok]
      by_cases hj : j = 8#usize
      · simp only [if_pos hj]
        cases hs : AspisR137Transcript.transcript.Transcript.squeeze_block s with
        | fail e => simp only [hs, bind_tc_fail]
        | div => simp only [hs, bind_tc_div]
        | ok x =>
          rcases x with ⟨b1,s1⟩
          simp only [hs, bind_tc_ok]
          cases hw : R137SamplerWordRead.sourceRead b1 0#usize with
          | fail e => simp [hw]
          | div => simp [hw]
          | ok pair =>
              rcases pair with ⟨word,j2⟩
              simp only [hw, bind_tc_ok, R137SamplerInnerStep.decideWord]
              by_cases hm : (word &&& AspisR137Transcript.field.P !=
                  AspisR137Transcript.field.P) = true
              · simp only [if_pos hm, control, finished, bind_tc_ok]
              · simp only [if_neg hm, control, pending, bind_tc_ok]
                simpa only [transcript.Transcript.challenge_qm31_loop0_loop0,
                  AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0,
                  R137SamplerInnerStep.factor, R137SamplerInnerStep.factored,
                  R137SamplerInnerStep.decideWord, R137SamplerInnerStep.nextRange,
                  SamplerOuterExecution.range_next, bind_tc_ok]
                  using ih (R137SamplerInnerStep.nextRange r hr) s1 b1 j2 hn'
      · simp only [if_neg hj]
        cases hw : R137SamplerWordRead.sourceRead b j with
        | fail e => simp [hw]
        | div => simp [hw]
        | ok pair =>
            rcases pair with ⟨word,j2⟩
            simp only [hw, bind_tc_ok, R137SamplerInnerStep.decideWord]
            by_cases hm : (word &&& AspisR137Transcript.field.P !=
                AspisR137Transcript.field.P) = true
            · simp only [if_pos hm, control, finished, bind_tc_ok]
            · simp only [if_neg hm, control, pending, bind_tc_ok]
              simpa only [transcript.Transcript.challenge_qm31_loop0_loop0,
                AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0,
                R137SamplerInnerStep.factor, R137SamplerInnerStep.factored,
                R137SamplerInnerStep.decideWord, R137SamplerInnerStep.nextRange,
                  SamplerOuterExecution.range_next, bind_tc_ok]
                using ih (R137SamplerInnerStep.nextRange r hr) s b j2 hn'

theorem eight_attempts_map
    (s : AspisR137Transcript.transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (limb : U32) :
    transcript.Transcript.challenge_qm31_loop0_loop0
      {start := 0#u32, «end» := transcript.CHALLENGE_RETRY_LIMIT}
      (fromR137 s) b j limb = (do
        let v ← AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0
          {start := 0#u32, «end» := AspisR137Transcript.transcript.CHALLENGE_RETRY_LIMIT}
          s b j limb
        ok (finished v)) := by
  simpa only [transcript.CHALLENGE_RETRY_LIMIT,
    AspisR137Transcript.transcript.CHALLENGE_RETRY_LIMIT] using
    loop_map 8 {start := 0#u32, «end» := 8#u32} s b j limb (by rfl)

#print axioms eight_attempts_map
#print axioms body_map
#print axioms loop_map
end AspisV8R19.R169InnerSamplerExecution
