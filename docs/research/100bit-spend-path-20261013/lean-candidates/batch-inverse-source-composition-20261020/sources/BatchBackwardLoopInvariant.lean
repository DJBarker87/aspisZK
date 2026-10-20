import BatchBackwardVecFacts
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

theorem backward_loop_success_inverses (mul : Mul) (hr : RefinesMul mul)
    (flat pref : Vec U32)
    (hprefsize : flat.val.length ≤ pref.val.length)
    (hprefix : ∀ (j : Nat) (hj : j < flat.val.length) (hp : j < pref.val.length),
      decode (pref.val[j]'hp) = ((flat.val.map decode).take j).prod)
    (hnonzero : ∀ x ∈ flat.val, decode x ≠ 0)
    (iter : ReverseRange) (suffix : U32) (state out : Vec U32)
    (hstart : iter.iter.start = 0#usize)
    (hbound : iter.iter.end.val ≤ flat.val.length)
    (hlen : state.val.length = flat.val.length)
    (hsuffix : decode suffix = ((flat.val.map decode).take iter.iter.end.val).prod⁻¹)
    (hgood : ∀ i, iter.iter.end.val ≤ i → i < flat.val.length → atM state i = (atM flat i)⁻¹)
    (hrun : backward_loop mul iter flat pref suffix state = .ok out) :
    out.val.length = flat.val.length ∧
      ∀ i, i < flat.val.length → atM out i = (atM flat i)⁻¹ := by
  induction hfuel : iter.iter.end.val generalizing iter suffix state with
  | zero =>
    have hstop : iter.iter.end.val ≤ iter.iter.start.val := by rw [hfuel]; exact Nat.zero_le _
    have hn := reverse_next_done iter hstop
    have hd : backward_loop mul iter flat pref suffix state = .ok state := by
      unfold backward_loop
      rw [loop.eq_def]
      simp only [backward_loop.body,hn,bind_tc_ok]
      rfl
    have he : state = out := Result.ok.inj (hd.symm.trans hrun)
    subst out
    exact ⟨hlen,fun i hi => hgood i (by rw [hfuel]; exact Nat.zero_le _) hi⟩
  | succ n ih =>
    have hpos : 0 < iter.iter.end.val := by omega
    let j := Usize.wrapping_sub iter.iter.end 1#usize
    have hjval : j.val = n := by
      rw [wrapping_sub_one_val _ (by omega)]
      omega
    let nextIter : ReverseRange := ⟨{iter.iter with «end»:=j}⟩
    let step := fun s : ReverseRange × U32 × Vec U32 => backward_loop.body mul flat pref s.1 s.2.1 s.2.2
    have hloop : Aeneas.Std.loop step (iter,suffix,state) = .ok out := hrun
    rcases loop_success_cases step (iter,suffix,state) out hloop with hd | ⟨st,hc,ht⟩
    · obtain ⟨v,w,hp,hf,he,_,_⟩ := backward_body_step mul hr flat pref state suffix iter (.done out)
        hstart hpos hbound (hbound.trans hprefsize) (by omega) hd
      cases he
    · rcases st with ⟨iter1,suffix1,state1⟩
      obtain ⟨v,w,hp,hf,he,hw,hv⟩ := backward_body_step mul hr flat pref state suffix iter
        (.cont (iter1,suffix1,state1)) hstart hpos hbound (hbound.trans hprefsize) (by omega) hc
      have htup := ControlFlow.cont.inj he
      have hiEq : iter1 = nextIter := congrArg Prod.fst htup
      have hsEq : suffix1 = v := congrArg (fun t => t.2.1) htup
      have hstEq : state1 = state.set j w := congrArg (fun t => t.2.2) htup
      have hjn : iter.iter.end.val = j.val + 1 := by omega
      obtain ⟨hwInv,hvInv⟩ := field_step_inverse flat pref suffix w v iter.iter.end.val j.val hf hp
        hjn hsuffix (hprefix j.val hf hp) hnonzero hw hv
      have hgood1 : ∀ i, nextIter.iter.end.val ≤ i → i < flat.val.length →
          atM (state.set j w) i = (atM flat i)⁻¹ := by
        intro i hlo hhi
        have hjlt : j.val < state.val.length := by omega
        by_cases hi : i = j.val
        · subst i
          rw [atM_set_self state j w hjlt,atM_get flat j.val hf]
          exact hwInv
        · rw [atM_set_ne state j w i (Ne.symm hi)]
          apply hgood i _ hhi
          change j.val ≤ i at hlo
          omega
      have hrun1 : backward_loop mul nextIter flat pref v (state.set j w) = .ok out := by
        rw [hiEq,hsEq,hstEq] at ht
        exact ht
      have hs1 : nextIter.iter.start = 0#usize := hstart
      have hb1 : nextIter.iter.end.val ≤ flat.val.length := by change j.val ≤ flat.val.length; omega
      have hl1 : (state.set j w).val.length = flat.val.length := by rw [set_length,hlen]
      exact ih nextIter v (state.set j w) hs1 hb1 hl1 hvInv hgood1 hrun1 hjval

#print axioms backward_loop_success_inverses
end AspisR1BatchBackward.Proof
