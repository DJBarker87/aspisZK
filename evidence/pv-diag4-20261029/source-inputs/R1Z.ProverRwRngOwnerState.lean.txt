import R1Z.ProverRwRngOwnerDraw
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerState
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerEvents ProverRwRngOwnerDraw
variable [ErasureFns]

def providerOf : ControlFlow State (Tape × Status) → Tape
  | .cont s => s.1
  | .done r => r.1

def Produces {A : Type} (p : A → Prop) (r : Result A) : Prop :=
  ∀ a, r = .ok a → p a

theorem produces_bind {A B : Type} (p : B → Prop) (x : Result A)
    (k : A → Result B) (h : ∀ a, Produces p (k a)) : Produces p (x >>= k) := by
  cases x with
  | ok a => exact h a
  | fail e => intro next impossible; cases impossible
  | div => intro next impossible; cases impossible

theorem afterFill_provider (nonce : Array U8 32#usize) (retry : Usize)
    (reply : (Tape × core.result.Result Unit U8) × Array U8 64#usize) :
    Produces (fun flow => providerOf flow = reply.1.1) (afterFill nonce retry reply) := by
  rcases reply with ⟨⟨after,status⟩,block⟩
  have again : Produces (fun flow => providerOf flow = after)
      (do let next ← retry + 1#usize
          .ok (.cont (after,next)) : Result (ControlFlow State (Tape × Status))) := by
    apply produces_bind
    intro next flow h
    cases h
    rfl
  unfold afterFill
  cases status with
  | Err e => intro flow h; cases h; rfl
  | Ok u =>
    simp only [zeroize.Zeroizing.new,zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,bind_tc_ok,Aeneas.Std.uncurry]
    apply produces_bind
    rintro ⟨s,back⟩
    try simp only [Aeneas.Std.uncurry,bind_tc_ok]
    apply produces_bind
    intro firstHalf
    apply produces_bind
    intro copiedFirst
    apply produces_bind
    rintro ⟨s2,back2⟩
    try simp only [Aeneas.Std.uncurry,bind_tc_ok]
    apply produces_bind
    intro secondHalf
    apply produces_bind
    intro copiedSecond
    apply produces_bind
    intro firstNonzero
    split
    · apply produces_bind
      intro secondNonzero
      split
      · intro flow h; cases h; rfl
      · exact again
    · exact again

/-- Actual indexed primitive event: one checked increment, immutable reply
sequence, and the complete selected block/status, including partial errors. -/
theorem fill_event (p : Tape) (input : Array U8 64#usize)
    (reply : (Tape × core.result.Result Unit U8) × Array U8 64#usize)
    (draw : Tape.Insts.Prover_rw_rng_preflightDraw64.fill p input = .ok reply) :
    reply.1.1.replies = p.replies ∧ reply.1.1.used.val = p.used.val + 1 ∧
      p.replies.val[p.used.val]? = some (reply.2,reply.1.2) := by
  rcases p with ⟨⟨replies,bound⟩,used⟩
  by_cases inside : used.val < replies.length
  · have fill := ProverRwRngTape.fill_at replies bound used inside input
    have one : (1#usize).val = 1 := by scalar_tac
    have safe : used.val + (1#usize).val ≤ Usize.max := by omega
    obtain ⟨next,add,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := used) (y := 1#usize) safe)
    simp only [add,bind_tc_ok] at fill
    change Tape.Insts.Prover_rw_rng_preflightDraw64.fill
      (ProverRwRngTape.tape replies bound used) input = .ok reply at draw
    rw [fill] at draw
    cases draw
    refine ⟨rfl,?_,?_⟩
    · simpa only [ProverRwRngTape.tape,one] using hv
    · simp only [ProverRwRngTape.tape,List.getElem?_eq_getElem inside]
  · unfold Tape.Insts.Prover_rw_rng_preflightDraw64.fill at draw
    have guard : ¬ used < alloc.vec.Vec.len (⟨replies,bound⟩ : alloc.vec.Vec ProverRwRngTape.Reply) := inside
    simp only [guard,massert,if_false,bind_tc_fail] at draw
    cases draw

theorem body_state (nonce : Array U8 32#usize) (p : Tape) (retry : Usize)
    (flow : ControlFlow State (Tape × Status)) (step : newBody nonce (p,retry) = .ok flow) :
    if retry < 16#usize then
      (providerOf flow).replies = p.replies ∧ (providerOf flow).used.val = p.used.val + 1
    else providerOf flow = p := by
  rw [draw_factor] at step
  split at step
  · rename_i below
    simp only [below,if_true]
    cases draw : Tape.Insts.Prover_rw_rng_preflightDraw64.fill p (Array.repeat 64#usize 0#u8) with
    | fail e => rw [draw] at step; cases step
    | div => rw [draw] at step; cases step
    | ok reply =>
      rw [draw] at step
      have returned := afterFill_provider nonce retry reply flow step
      have event := fill_event p (Array.repeat 64#usize 0#u8) reply draw
      rw [returned]
      exact ⟨event.1,event.2.1⟩
  · rename_i stop
    simp only [stop,if_false]
    cases step
    rfl

#print axioms produces_bind
#print axioms afterFill_provider
#print axioms fill_event
#print axioms body_state
end R1Z.ProverRwRngOwnerState
