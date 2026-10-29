import R1Z.ProverRwRngOwnerStep
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerInduction
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep
variable [ErasureFns]

def Continues {A B : Type} (p : A → Prop) (r : Result (ControlFlow A B)) : Prop :=
  ∀ next, r = .ok (.cont next) → p next

theorem continues_bind {A B C : Type} (p : B → Prop) (x : Result A)
    (k : A → Result (ControlFlow B C)) (h : ∀ a, Continues p (k a)) :
    Continues p (x >>= k) := by
  cases x with
  | ok a => exact h a
  | fail e => intro next impossible; cases impossible
  | div => intro next impossible; cases impossible

theorem add_progress (retry : Usize) (below : retry < 16#usize) (after : Tape) :
    Continues (fun next : Tape × Usize => next.2.val = retry.val + 1)
      (do let next ← retry + 1#usize
          .ok (.cont (after,next)) : Result (ControlFlow (Tape × Usize) (Tape × Status))) := by
  have safe : retry.val + (1#usize).val ≤ Usize.max := by scalar_tac
  obtain ⟨next,he,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := retry) (y := 1#usize) safe)
  intro state h
  rw [he] at h
  simp only [bind_tc_ok,Result.ok.injEq,ControlFlow.cont.injEq] at h
  subst state
  have one : (1#usize).val = 1 := by scalar_tac
  simpa only [one] using hv

theorem body_progress (nonce : Array U8 32#usize) (p : Tape) (retry : Usize) :
    Continues (fun next : Tape × Usize => retry < 16#usize ∧ next.2.val = retry.val + 1)
      (StateOnlyAttemptSecrets.generate_with_loop.body
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce 16#usize p retry) := by
  by_cases below : retry < 16#usize
  · have progress : ∀ after : Tape,
        Continues (fun next : Tape × Usize => retry < 16#usize ∧ next.2.val = retry.val + 1)
          (do let next ← retry + 1#usize
              .ok (.cont (after,next)) : Result (ControlFlow (Tape × Usize) (Tape × Status))) := by
      intro after next h
      exact ⟨below,add_progress retry below after next h⟩
    unfold StateOnlyAttemptSecrets.generate_with_loop.body
    rw [if_pos below]
    simp only [zeroize.Zeroizing.new,zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok]
    apply continues_bind
    rintro ⟨⟨after,status⟩,block⟩
    cases status with
    | Err e => intro next h; cases h
    | Ok u =>
      try simp only [Aeneas.Std.uncurry,bind_tc_ok]
      apply continues_bind
      rintro ⟨s,back⟩
      try simp only [Aeneas.Std.uncurry,bind_tc_ok]
      apply continues_bind
      intro firstHalf
      apply continues_bind
      intro copiedFirst
      apply continues_bind
      rintro ⟨s2,back2⟩
      try simp only [Aeneas.Std.uncurry,bind_tc_ok]
      apply continues_bind
      intro secondHalf
      apply continues_bind
      intro copiedSecond
      apply continues_bind
      intro firstNonzero
      split
      · apply continues_bind
        intro secondNonzero
        split
        · intro next h; cases h
        · exact progress _
      · exact progress _
  · unfold StateOnlyAttemptSecrets.generate_with_loop.body
    simp only [below,if_false]
    intro next h
    cases h

#print axioms continues_bind
#print axioms add_progress
#print axioms body_progress

end R1Z.ProverRwRngOwnerInduction
