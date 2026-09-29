import AspisV8R19.SamplerObservedSqueeze
import AspisV8R19.SamplerInnerStep

/-! Exact observer transitions of the instrumented generated inner body.
Existing-block reads and exhaustion add no events; rollover appends exactly
the observed squeeze events. This is not the full rejection-loop theorem. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedInnerStep
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler
open SamplerWordRead SamplerInnerStep SamplerObservation SamplerObservedLaws

def factored (limb : field.M31) (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) : Observed (ControlFlow Pending Finished) := do
  let (o,r1) ← core.iter.range.IteratorRange.next core.iter.range.StepU32 r
  match o with
  | none => pure (.done (s,b,j,limb,false))
  | some _ =>
      let (s1,b1,j1) ← if j = 8#usize then do
          let (b2,s2) ← SamplerObservedSource.squeeze_block s
          pure (s2,b2,0#usize)
        else pure (s,b,j)
      let (word,j2) ← read b1 j1
      pure (decideWord r1 s1 b1 j2 word)

theorem factor (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize) :
    SamplerObservedSource.challenge_qm31_loop0_loop0.body limb r s b j =
      factored limb r s b j := by
  funext history
  cases hi : core.iter.range.IteratorRange.next core.iter.range.StepU32 r with
  | fail e => simp [SamplerObservedSource.challenge_qm31_loop0_loop0.body,factored,
      hi,bind_apply,lift_apply]
  | div => simp [SamplerObservedSource.challenge_qm31_loop0_loop0.body,factored,
      hi,bind_apply,lift_apply]
  | ok pair =>
      rcases pair with ⟨o,r1⟩
      cases o with
      | none => simp [SamplerObservedSource.challenge_qm31_loop0_loop0.body,factored,
          hi,bind_apply,lift_apply]
      | some v =>
          by_cases hj : j=8#usize <;>
            simp [SamplerObservedSource.challenge_qm31_loop0_loop0.body,factored,hi,hj,
              SamplerWordRead.read,decideWord,bind_apply,lift_apply,
              bind_assoc,bind_tc_ok,lift,apply_ite]

theorem exhausted (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hr : ¬r.start.val < r.end.val) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0.body limb r s b j history =
      .ok (.done (s,b,j,limb,false),history) := by
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_neg hr,bind_apply,
    lift_apply,bind_tc_ok,pure_apply]

theorem existing_block (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hr : r.start.val < r.end.val) (hj : j.val < 8) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0.body limb r s b j history =
      .ok (decideWord (nextRange r hr) s b (small (j.val+1) (by omega))
        (core.num.U32.from_le_bytes (four b (j.val*4) (by omega))),history) := by
  have hne : j ≠ 8#usize := by intro h; have := congrArg UScalar.val h; simp at this; omega
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_pos hr,bind_apply,
    lift_apply,bind_tc_ok,pure_apply,if_neg hne,read_success b j hj,nextRange]

theorem rollover (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize)
    (hr : r.start.val < r.end.val) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0.body limb r s b 8#usize history =
      (do
        let ((b1,s1),observed) ← SamplerObservedSource.squeeze_block s history
        ok (decideWord (nextRange r hr) s1 b1 (small 1 (by omega))
          (core.num.U32.from_le_bytes (four b1 0 (by omega))),observed)) := by
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_pos hr,bind_apply,
    lift_apply,bind_tc_ok,pure_apply,nextRange,ite_true]
  cases h : SamplerObservedSource.squeeze_block s history with
  | fail e => simp
  | div => simp
  | ok pair =>
      rcases pair with ⟨⟨b1,s1⟩,observed⟩
      simp only [bind_tc_ok,read_success b1 0#usize (by decide)]
      rfl

#print axioms factor
#print axioms exhausted
#print axioms existing_block
#print axioms rollover
end AspisV8R19.SamplerObservedInnerStep
