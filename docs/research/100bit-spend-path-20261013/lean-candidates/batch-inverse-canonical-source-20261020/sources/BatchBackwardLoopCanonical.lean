import BatchBackwardCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

private theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧ Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext,rfl,h⟩

theorem backward_loop_success_canonical (flat pref : Vec U32)
    (iter : ReverseRange) (suffix : U32) (state out : Vec U32)
    (hstart : iter.iter.start = 0#usize)
    (hbound : iter.iter.end.val ≤ state.val.length) (hcanon : CanonicalVec state)
    (hrun : backward_loop currentMul iter flat pref suffix state = .ok out) : CanonicalVec out := by
  induction hfuel : iter.iter.end.val generalizing iter suffix state with
  | zero =>
    have hstop : iter.iter.end.val ≤ iter.iter.start.val := by rw [hfuel]; exact Nat.zero_le _
    have hn := reverse_next_done iter hstop
    have hd : backward_loop currentMul iter flat pref suffix state = .ok state := by
      unfold backward_loop
      rw [loop.eq_def]
      simp only [backward_loop.body,hn,bind_tc_ok]
      rfl
    have he : state = out := Result.ok.inj (hd.symm.trans hrun)
    subst out
    exact hcanon
  | succ n ih =>
    have hpos : 0 < iter.iter.end.val := by omega
    let j := Usize.wrapping_sub iter.iter.end 1#usize
    have hjval : j.val = n := by rw [wrapping_sub_one_val _ (by omega)]; omega
    let nextIter : ReverseRange := ⟨{iter.iter with «end»:=j}⟩
    let step := fun s : ReverseRange × U32 × Vec U32 => backward_loop.body currentMul flat pref s.1 s.2.1 s.2.2
    have hloop : Aeneas.Std.loop step (iter,suffix,state) = .ok out := hrun
    rcases loop_success_cases step (iter,suffix,state) out hloop with hd | ⟨st,hc,ht⟩
    · obtain ⟨v,s,he,_,_⟩ := backward_body_canonical flat pref state suffix iter (.done out)
        hstart hpos hbound hcanon hd
      cases he
    · rcases st with ⟨iter1,suffix1,state1⟩
      obtain ⟨v,s,he,hcanon1,hlen1⟩ := backward_body_canonical flat pref state suffix iter
        (.cont (iter1,suffix1,state1)) hstart hpos hbound hcanon hc
      have htup := ControlFlow.cont.inj he
      have hiEq : iter1 = nextIter := congrArg Prod.fst htup
      have hsEq : suffix1 = v := congrArg (fun t => t.2.1) htup
      have hstEq : state1 = s := congrArg (fun t => t.2.2) htup
      have hrun1 : backward_loop currentMul nextIter flat pref v s = .ok out := by
        rw [hiEq,hsEq,hstEq] at ht
        exact ht
      have hs1 : nextIter.iter.start = 0#usize := hstart
      have hb1 : nextIter.iter.end.val ≤ s.val.length := by change j.val ≤ s.val.length; omega
      exact ih nextIter v s hs1 hb1 hcanon1 hrun1 hjval

#print axioms backward_loop_success_canonical
end AspisR1BatchBackward.Proof
