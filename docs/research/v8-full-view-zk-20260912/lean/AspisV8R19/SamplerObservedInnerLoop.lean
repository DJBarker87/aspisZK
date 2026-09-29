import AspisV8R19.SamplerObservedInnerStep
import AspisV8R19.SamplerInnerLoop

/-! Finite execution of the instrumented rejection loop with its observation
state. All backends are allowed; no successful or random draw is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedInnerLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler SamplerWordRead SamplerInnerStep
open SamplerInnerLoop (Cursor index index_val)
open SamplerObservation SamplerObservedLaws

def draw (c : Cursor) : Observed (Cursor × U32) :=
  if h : c.index.val < 8 then
    pure ({c with index:=⟨c.index.val+1,by omega⟩},
      core.num.U32.from_le_bytes (four c.block (c.index.val*4) (by omega)))
  else do
    let (b,s) ← SamplerObservedSource.squeeze_block c.state
    pure (⟨s,b,⟨1,by decide⟩⟩,core.num.U32.from_le_bytes (four b 0 (by omega)))

def bounded : Nat → Cursor → field.M31 → Observed Finished
  | 0,c,limb => pure (c.state,c.block,index c,limb,false)
  | n+1,c,limb => do
      let (c1,word) ← draw c
      let masked := word &&& field.P
      if masked != field.P then pure (c1.state,c1.block,index c1,masked,true)
      else bounded n c1 limb

theorem body_ready (limb : field.M31) (r : core.ops.range.Range U32)
    (c : Cursor) (hr : r.start.val < r.end.val) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0.body limb r c.state c.block (index c) history =
      (do
        let ((c1,word),observed) ← draw c history
        ok (decideWord (nextRange r hr) c1.state c1.block (index c1) word,observed)) := by
  by_cases hj : c.index.val < 8
  · rw [SamplerObservedInnerStep.existing_block limb r c.state c.block (index c) hr
      (by simpa only [index_val] using hj)]
    simp only [draw,dif_pos hj,pure_apply,bind_tc_ok,index,small_val]
  · have hv : c.index.val=8 := by have := c.index.isLt; omega
    have he : index c = 8#usize := by apply UScalar.eq_of_val_eq; exact hv
    rw [he,SamplerObservedInnerStep.rollover limb r c.state c.block hr]
    simp only [draw,dif_neg hj,bind_apply,pure_apply,bind_assoc,bind_tc_ok,index]

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32)
    (c : Cursor) (limb : field.M31) (hn : r.end.val-r.start.val=n) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0 r c.state c.block (index c) limb history =
      bounded n c limb history := by
  induction n generalizing r c history with
  | zero =>
      have hr : ¬r.start.val < r.end.val := by omega
      rw [SamplerObservedSource.challenge_qm31_loop0_loop0,loop_unfold]
      simp only [SamplerObservedInnerStep.exhausted limb r c.state c.block (index c) hr,
        bounded,pure_apply,bind_tc_ok]
  | succ n ih =>
      have hr : r.start.val < r.end.val := by omega
      have hn' : (nextRange r hr).end.val-(nextRange r hr).start.val=n := by
        change r.end.val-(r.start.val+1)=n; omega
      rw [SamplerObservedSource.challenge_qm31_loop0_loop0,loop_unfold]
      simp only [body_ready limb r c hr,bounded,bind_apply]
      cases hd : draw c history with
      | fail e => simp
      | div => simp
      | ok pair =>
          rcases pair with ⟨⟨c1,word⟩,observed⟩
          by_cases hw : word &&& field.P = field.P
          · simp only [bind_tc_ok,decideWord,hw,bne_self_eq_false,Bool.false_eq_true,if_false]
            simpa only [SamplerObservedSource.challenge_qm31_loop0_loop0] using
              ih (nextRange r hr) c1 hn' observed
          · have ht : (word &&& field.P != field.P)=true := bne_iff_ne.mpr hw
            simp only [bind_tc_ok,decideWord,ht,if_true,pure_apply]

theorem eight_attempts (c : Cursor) (limb : field.M31) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0_loop0
      {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
      c.state c.block (index c) limb history = bounded 8 c limb history := by
  apply loop_execution
  simp only [transcript.CHALLENGE_RETRY_LIMIT]
  rfl

#print axioms body_ready
#print axioms loop_execution
#print axioms eight_attempts
end AspisV8R19.SamplerObservedInnerLoop
