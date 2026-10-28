import NDG_ZeroStep
set_option autoImplicit false
namespace NDG_ZeroRun
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def AllZero (b : Slice U8) (start : Nat) : Prop :=
  ∀ j, start ≤ j → j < b.val.length → NDG_ZeroStep.byte b j=0#u8

theorem run (b : Slice U8) (i : Usize) (cap : b.val.length ≤ 65536)
    (bound : i.val ≤ b.val.length) :
    AdapterRw.r1_pool_adapter.owned.require_zero_loop b i =
      ok (if AllZero b i.val then none else some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
  classical
  have all : ∀ n : Nat, ∀ k : Usize, k.val ≤ b.val.length → b.val.length-k.val=n →
      AdapterRw.r1_pool_adapter.owned.require_zero_loop b k=ok (if AllZero b k.val then none else some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk hn
      by_cases terminal : b.val.length ≤ k.val
      · have good : AllZero b k.val := by intro j hj hb;omega
        unfold AdapterRw.r1_pool_adapter.owned.require_zero_loop
        rw [NDG_ZeroLoop.done _ _ _ (NDG_ZeroStep.terminal b k terminal),if_pos good]
      · have lt : k.val < b.val.length := by omega
        obtain ⟨next,value,step⟩ := NDG_ZeroStep.step b k cap lt
        by_cases good : NDG_ZeroStep.byte b k.val=0#u8
        · rw [if_neg (not_not.mpr good)] at step
          have recursive := ih (b.val.length-next.val) (by omega) next (by omega) rfl
          have suffix : AllZero b k.val ↔ AllZero b next.val := by
            constructor
            · intro h j hj hb;exact h j (by omega) hb
            · intro h j hj hb
              by_cases same : j=k.val
              · simpa only [same] using good
              · exact h j (by omega) hb
          unfold AdapterRw.r1_pool_adapter.owned.require_zero_loop
          rw [NDG_ZeroLoop.cont _ _ _ step]
          change AdapterRw.r1_pool_adapter.owned.require_zero_loop b next = _
          rw [recursive,propext suffix]
        · rw [if_pos good] at step
          have bad : ¬AllZero b k.val := by intro h;exact good (h k.val (by omega) lt)
          unfold AdapterRw.r1_pool_adapter.owned.require_zero_loop
          rw [NDG_ZeroLoop.done _ _ _ step,if_neg bad]
  exact all (b.val.length-i.val) i bound rfl

theorem value (b : Slice U8) (cap : b.val.length ≤ 65536) :
    AdapterRw.r1_pool_adapter.owned.require_zero b = ok
      (if AllZero b 0 then .Ok () else
        .Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized) := by
  classical
  unfold AdapterRw.r1_pool_adapter.owned.require_zero
  rw [run b 0#usize cap (by scalar_tac)]
  by_cases good : AllZero b 0
  · simp only [show (0#usize).val=0 from rfl,bind_tc_ok,good,ite_true]
  · simp only [show (0#usize).val=0 from rfl,bind_tc_ok,good,ite_false]

#print axioms run
#print axioms value
end NDG_ZeroRun
