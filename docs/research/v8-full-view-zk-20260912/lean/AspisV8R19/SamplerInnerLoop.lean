import AspisV8R19.SamplerInnerStep

/-! Bounded execution of the actual per-limb rejection loop. The cursor's
finite type records the source invariant, including the rollover position.
The backend remains arbitrary: no successful or uniform draw is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerInnerLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler SamplerWordRead SamplerInnerStep

structure Cursor where
  state : transcript.Transcript
  block : Array U8 32#usize
  index : Fin 9

def index (c : Cursor) : Usize := small c.index.val (by have := c.index.isLt; omega)

def draw (c : Cursor) : Result (Cursor × U32) :=
  if h : c.index.val < 8 then
    .ok ({c with index:=⟨c.index.val+1,by omega⟩},
      core.num.U32.from_le_bytes (four c.block (c.index.val*4) (by omega)))
  else do
    let (b,s) ← transcript.Transcript.squeeze_block c.state
    ok (⟨s,b,⟨1,by decide⟩⟩,core.num.U32.from_le_bytes (four b 0 (by omega)))

def bounded : Nat → Cursor → field.M31 → Result Finished
  | 0,c,limb => .ok (c.state,c.block,index c,limb,false)
  | n+1,c,limb => do
      let (c1,word) ← draw c
      let masked := word &&& field.P
      if masked != field.P then ok (c1.state,c1.block,index c1,masked,true)
      else bounded n c1 limb

theorem index_val (c : Cursor) : (index c).val = c.index.val := rfl
theorem index_bound (c : Cursor) : (index c).val ≤ 8 := by
  rw [index_val]; have := c.index.isLt; omega

theorem body_ready (limb : field.M31) (r : core.ops.range.Range U32)
    (c : Cursor) (hr : r.start.val < r.end.val) :
    transcript.Transcript.challenge_qm31_loop0_loop0.body limb r c.state c.block (index c) =
      (do
        let (c1,word) ← draw c
        ok (decideWord (nextRange r hr) c1.state c1.block (index c1) word)) := by
  by_cases hj : c.index.val < 8
  · rw [existing_block limb r c.state c.block (index c) hr (by simpa only [index_val] using hj)]
    simp only [draw,dif_pos hj,bind_tc_ok,index,small_val]
  · have hv : c.index.val=8 := by have := c.index.isLt; omega
    have he : index c = 8#usize := by apply UScalar.eq_of_val_eq; exact hv
    rw [he,rollover limb r c.state c.block hr]
    simp only [draw,dif_neg hj,bind_assoc,bind_tc_ok,index]

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32)
    (c : Cursor) (limb : field.M31) (hn : r.end.val-r.start.val=n) :
    transcript.Transcript.challenge_qm31_loop0_loop0 r c.state c.block (index c) limb =
      bounded n c limb := by
  induction n generalizing r c with
  | zero =>
      have hr : ¬r.start.val < r.end.val := by omega
      rw [transcript.Transcript.challenge_qm31_loop0_loop0,loop.eq_def]
      simp only [exhausted limb r c.state c.block (index c) hr,bounded]
  | succ n ih =>
      have hr : r.start.val < r.end.val := by omega
      have hn' : (nextRange r hr).end.val-(nextRange r hr).start.val=n := by
        change r.end.val-(r.start.val+1)=n; omega
      rw [transcript.Transcript.challenge_qm31_loop0_loop0,loop.eq_def]
      simp only [body_ready limb r c hr,bounded]
      cases hd : draw c with
      | fail e => simp
      | div => simp
      | ok pair =>
          rcases pair with ⟨c1,word⟩
          by_cases hw : word &&& field.P = field.P
          · simp only [bind_tc_ok,decideWord,hw,bne_self_eq_false,Bool.false_eq_true,if_false]
            simpa only [transcript.Transcript.challenge_qm31_loop0_loop0] using ih (nextRange r hr) c1 hn'
          · have ht : (word &&& field.P != field.P)=true := by exact bne_iff_ne.mpr hw
            simp only [bind_tc_ok,decideWord,ht,if_true]

theorem eight_attempts (c : Cursor) (limb : field.M31) :
    transcript.Transcript.challenge_qm31_loop0_loop0
      {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
      c.state c.block (index c) limb = bounded 8 c limb := by
  apply loop_execution
  simp only [transcript.CHALLENGE_RETRY_LIMIT]
  rfl

theorem zero_no_draw (c : Cursor) (limb : field.M31) :
    bounded 0 c limb = .ok (c.state,c.block,index c,limb,false) := rfl

theorem accepted_stops (n : Nat) (c c1 : Cursor) (limb word : U32)
    (hd : draw c = .ok (c1,word)) (hw : word &&& field.P ≠ field.P) :
    bounded (n+1) c limb = .ok (c1.state,c1.block,index c1,word &&& field.P,true) := by
  have ht : (word &&& field.P != field.P)=true := bne_iff_ne.mpr hw
  simp only [bounded,hd,bind_tc_ok,ht,if_true]
theorem rejected_advances (n : Nat) (c c1 : Cursor) (limb word : U32)
    (hd : draw c = .ok (c1,word)) (hw : word &&& field.P = field.P) :
    bounded (n+1) c limb = bounded n c1 limb := by
  simp only [bounded,hd,bind_tc_ok,hw,bne_self_eq_false,Bool.false_eq_true,if_false]

theorem result_invariant (n : Nat) (c : Cursor) (limb : field.M31)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize) (value : field.M31)
    (accepted : Bool) (h : bounded n c limb = .ok (s,b,j,value,accepted)) :
    j.val ≤ 8 ∧ (accepted=true → value.val < 2147483647) ∧
      (accepted=false → value=limb) := by
  induction n generalizing c with
  | zero =>
      simp only [bounded,Result.ok.injEq,Prod.mk.injEq] at h
      rcases h with ⟨hs,hb,hj,hv,ha⟩
      subst j; subst value; subst accepted
      simp [index_bound]
  | succ n ih =>
      simp only [bounded] at h
      cases hd : draw c with
      | fail e => simp [hd] at h
      | div => simp [hd] at h
      | ok pair =>
          rcases pair with ⟨c1,word⟩
          by_cases hw : word &&& field.P = field.P
          · simp only [hd,bind_tc_ok,hw,bne_self_eq_false,Bool.false_eq_true,if_false] at h
            exact ih c1 h
          · have ht : (word &&& field.P != field.P)=true := bne_iff_ne.mpr hw
            simp only [hd,bind_tc_ok,ht,if_true,Result.ok.injEq,Prod.mk.injEq] at h
            rcases h with ⟨hs,hb,hj,hv,ha⟩
            subst j; subst value; subst accepted
            exact ⟨index_bound c1,fun _ => accepted_canonical word hw,by simp⟩

theorem source_result_invariant (n : Nat) (r : core.ops.range.Range U32)
    (s s1 : transcript.Transcript) (b b1 : Array U8 32#usize) (j j1 : Usize)
    (limb value : field.M31) (accepted : Bool)
    (hj : j.val ≤ 8) (hn : r.end.val-r.start.val=n)
    (h : transcript.Transcript.challenge_qm31_loop0_loop0 r s b j limb =
      .ok (s1,b1,j1,value,accepted)) :
    j1.val ≤ 8 ∧ (accepted=true → value.val < 2147483647) ∧
      (accepted=false → value=limb) := by
  let c : Cursor := ⟨s,b,⟨j.val,by omega⟩⟩
  have hc : index c=j := by apply UScalar.eq_of_val_eq; rfl
  have he := loop_execution n r c limb hn
  rw [hc] at he
  have hb : bounded n c limb = .ok (s1,b1,j1,value,accepted) := he.symm.trans h
  exact result_invariant n c limb s1 b1 j1 value accepted hb

#print axioms index_val
#print axioms index_bound
#print axioms body_ready
#print axioms loop_execution
#print axioms eight_attempts
#print axioms zero_no_draw
#print axioms accepted_stops
#print axioms rejected_advances
#print axioms result_invariant
#print axioms source_result_invariant
end AspisV8R19.SamplerInnerLoop
