import R1Z.PV_RunJoin_EntropyStep

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EntropyCapacity
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerDraw ProverRwRngOwnerEvents ProverRwRngOwnerState
open ProverRwRngOwnerInduction
variable [ErasureFns]

theorem fill_total (p : Tape) (inside : p.used.val < p.replies.val.length)
    (input : Array U8 64#usize) :
    ∃ out, Tape.Insts.Prover_rw_rng_preflightDraw64.fill p input = .ok out := by
  rcases p with ⟨⟨replies,bound⟩,used⟩
  have safe : used.val + (1#usize).val ≤ Usize.max := by
    change used.val < replies.length at inside
    have one : (1#usize).val = 1 := by scalar_tac
    omega
  obtain ⟨next,add,_⟩ := WP.spec_imp_exists (Usize.add_spec (x := used) (y := 1#usize) safe)
  have fill := ProverRwRngTape.fill_at replies bound used inside input
  rw [add] at fill
  exact ⟨_,fill⟩

theorem body_total (nonce : Array U8 32#usize) (p : Tape) (retry : Usize)
    (capacity : p.used.val + (16 - retry.val) ≤ p.replies.val.length) :
    ∃ flow, newBody nonce (p,retry) = .ok flow := by
  by_cases below : retry < 16#usize
  · have inside : p.used.val < p.replies.val.length := by
      have retryBound : retry.val < 16 := below
      omega
    obtain ⟨reply,draw⟩ := fill_total p inside (Array.repeat 64#usize 0#u8)
    obtain ⟨flow,tail⟩ := PV_RunJoin_EntropyStep.afterFill_total nonce retry below reply
    exact ⟨flow,by rw [draw_factor,if_pos below,draw,bind_tc_ok,tail]⟩
  · exact ⟨.done (p,.Err .RepeatedZeroBlock),by rw [draw_factor,if_neg below]⟩

theorem loop_total (nonce : Array U8 32#usize) (p : Tape) (retry : Usize)
    (capacity : p.used.val + (16 - retry.val) ≤ p.replies.val.length) :
    ∃ out, StateOnlyAttemptSecrets.generate_with_loop
      Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry = .ok out := by
  suffices ∀ fuel p retry, 17 - retry.val = fuel →
      p.used.val + (16 - retry.val) ≤ p.replies.val.length →
      ∃ out, StateOnlyAttemptSecrets.generate_with_loop
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry = .ok out by
    exact this _ p retry rfl capacity
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro p retry hf capacity
    obtain ⟨flow,step⟩ := body_total nonce p retry capacity
    cases flow with
    | done result =>
      refine ⟨result,?_⟩
      change loop (newBody nonce) (p,retry) = _
      rw [loop,step]
    | cont next =>
      obtain ⟨below,increased⟩ := body_progress nonce p retry next step
      have inventory := body_state nonce p retry (.cont next) step
      simp only [below,if_true,providerOf] at inventory
      have retryBound : retry.val < 16 := below
      have less : 17 - next.2.val < fuel := by omega
      have nextCapacity : next.1.used.val + (16 - next.2.val) ≤ next.1.replies.val.length := by
        rw [inventory.1,inventory.2]
        omega
      obtain ⟨result,tail⟩ := ih _ less next.1 next.2 rfl nextCapacity
      refine ⟨result,?_⟩
      change loop (newBody nonce) (p,retry) = _
      rw [loop,step]
      exact tail

/-- Full prototype owner totality with room for sixteen draws. A native OS
error is a returned status; no success, nonzero nonce or status law is assumed. -/
theorem owner_total (nonce : Array U8 32#usize) (p : Tape)
    (capacity : p.used.val + 16 ≤ p.replies.val.length) :
    ∃ after status, owner nonce p = .ok (after,status) := by
  obtain ⟨admitted,scan⟩ := PV_RunJoin_EntropyTotal.nonzero_total nonce
  cases admitted with
  | false =>
    exact ⟨p,.Err .RepeatedZeroBlock,by
      simp only [owner,StateOnlyAttemptSecrets.generate_with,scan,bind_tc_ok,Bool.false_eq_true,if_false]⟩
  | true =>
    obtain ⟨⟨after,status⟩,run⟩ := loop_total nonce p 0#usize capacity
    exact ⟨after,status,by
      simp only [owner,StateOnlyAttemptSecrets.generate_with,scan,bind_tc_ok,if_true]
      simpa only [ENTROPY_RETRY_LIMIT] using run⟩

#print axioms fill_total
#print axioms body_total
#print axioms loop_total
#print axioms owner_total
end R1Z.PV_RunJoin_EntropyCapacity
