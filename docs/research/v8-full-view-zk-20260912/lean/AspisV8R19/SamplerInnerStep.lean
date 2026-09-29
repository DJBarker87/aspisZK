import AspisV8R19.SamplerWordRead
import AspisV8R19.SamplerOuterExecution

/-! Exact generated inner-loop body, including block rollover and rejection.
This is a one-step theorem, not the full four-limb sampler theorem. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerInnerStep
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler SamplerWordRead

abbrev Pending := (core.ops.range.Range U32) × transcript.Transcript ×
  (Array U8 32#usize) × Usize
abbrev Finished := transcript.Transcript × (Array U8 32#usize) × Usize × field.M31 × Bool

def decideWord (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (word : U32) : ControlFlow Pending Finished :=
  let masked := word &&& field.P
  if masked != field.P then .done (s,b,j,masked,true) else .cont (r,s,b,j)

def factored (limb : field.M31) (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) : Result (ControlFlow Pending Finished) := do
  let (o,r1) ← core.iter.range.IteratorRange.next core.iter.range.StepU32 r
  match o with
  | none => ok (.done (s,b,j,limb,false))
  | some _ =>
      let (s1,b1,j1) ← if j = 8#usize then do
          let (b2,s2) ← transcript.Transcript.squeeze_block s
          ok (s2,b2,0#usize)
        else ok (s,b,j)
      let (word,j2) ← read b1 j1
      ok (decideWord r1 s1 b1 j2 word)

theorem factor (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r s b j =
      factored limb r s b j := by
  simp only [transcript.Transcript.challenge_qm31_loop0_loop0.body,factored,
    SamplerWordRead.read,decideWord,bind_assoc,bind_tc_ok,lift,apply_ite]
  rfl

def nextRange (r : core.ops.range.Range U32) (hr : r.start.val < r.end.val) :
    core.ops.range.Range U32 :=
  {start:=UScalar.ofNatCore (r.start.val+1) (by have := r.end.hBounds; omega), «end»:=r.end}

theorem exhausted (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hr : ¬r.start.val < r.end.val) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r s b j =
      .ok (.done (s,b,j,limb,false)) := by
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_neg hr,bind_tc_ok]

theorem existing_block (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hr : r.start.val < r.end.val) (hj : j.val < 8) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r s b j =
      .ok (decideWord (nextRange r hr) s b (small (j.val+1) (by omega))
        (core.num.U32.from_le_bytes (four b (j.val*4) (by omega)))) := by
  have hne : j ≠ 8#usize := by intro h; have := congrArg UScalar.val h; simp at this; omega
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_pos hr,bind_tc_ok,
    if_neg hne,read_success b j hj,nextRange]

theorem rollover (limb : field.M31) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (b : Array U8 32#usize)
    (hr : r.start.val < r.end.val) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r s b 8#usize =
      (do
        let (b1,s1) ← transcript.Transcript.squeeze_block s
        ok (decideWord (nextRange r hr) s1 b1 (small 1 (by omega))
          (core.num.U32.from_le_bytes (four b1 0 (by omega))))) := by
  rw [factor]
  simp only [factored,SamplerOuterExecution.range_next,dif_pos hr,bind_tc_ok,
    nextRange]
  cases h : transcript.Transcript.squeeze_block s with
  | fail e => rfl
  | div => rfl
  | ok pair =>
      rcases pair with ⟨b1,s1⟩
      simp only [bind_tc_ok,read_success b1 0#usize (by decide)]
      rfl

theorem accepted (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (word : U32) (h : word &&& field.P ≠ field.P) :
    decideWord r s b j word = .done (s,b,j,word &&& field.P,true) := by
  simp [decideWord,h]
theorem rejected (r : core.ops.range.Range U32) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (word : U32) (h : word &&& field.P = field.P) :
    decideWord r s b j word = .cont (r,s,b,j) := by
  simp [decideWord,h]

#print axioms factor
#print axioms exhausted
#print axioms existing_block
#print axioms rollover
#print axioms accepted
#print axioms rejected
end AspisV8R19.SamplerInnerStep
