import NCO_GlobalWord
import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Inner

def GoodFrom (payload : Slice U8) (i first : Nat) : Prop :=
  ∀ j, first ≤ j → j < 8 → NCO_GlobalWord.Good payload i j

theorem start (payload : Slice U8) (i j : Usize)
    (cap : payload.val.length ≤ 3712) (hi : i.val < payload.val.length/32) (hj : j.val < 8) :
    ∃ successor : Usize, successor.val = j.val+1 ∧
      NCO_ParserRef.validate_ref_loop0_loop0.body payload i j =
        if NCO_GlobalWord.Good payload i.val j.val then ok (.cont successor)
        else ok (.done (i,0#u32)) := by
  obtain ⟨successor,inc,step⟩ := NCO_GlobalWord.step payload i j cap hi hj
  refine ⟨successor,inc,?_⟩
  rw [step]
  unfold NCO_GlobalWord.Good
  split_ifs <;> simp_all <;> scalar_tac

theorem run (payload : Slice U8) (i j row_next : Usize)
    (cap : payload.val.length ≤ 3712) (hi : i.val < payload.val.length/32)
    (hj : j.val ≤ 8) (advance : i + 1#usize = ok row_next) :
    NCO_ParserRef.validate_ref_loop0_loop0 payload i j =
      ok (if GoodFrom payload i.val j.val then (row_next,1#u32) else (i,0#u32)) := by
  classical
  have all : ∀ n : Nat, ∀ k : Usize, k.val ≤ 8 → 8-k.val=n →
      NCO_ParserRef.validate_ref_loop0_loop0 payload i k =
        ok (if GoodFrom payload i.val k.val then (row_next,1#u32) else (i,0#u32)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk hn
      by_cases terminal : 8 ≤ k.val
      · have good : GoodFrom payload i.val k.val := by
          intro l hl hl8
          omega
        have step := NCO_LoopSteps.inner_done payload i k row_next terminal advance
        unfold NCO_ParserRef.validate_ref_loop0_loop0
        rw [NCO_LoopSteps.loop_done _ _ _ step, if_pos good]
      · have lt : k.val < 8 := by omega
        obtain ⟨successor,inc,step⟩ := start payload i k cap hi lt
        by_cases good : NCO_GlobalWord.Good payload i.val k.val
        · rw [if_pos good] at step
          have bound : successor.val ≤ 8 := by omega
          have decrease : 8-successor.val<n := by omega
          have recursive := ih (8-successor.val) decrease successor bound rfl
          have suffix : GoodFrom payload i.val k.val ↔ GoodFrom payload i.val successor.val := by
            constructor
            · intro h l hl hl8
              exact h l (by omega) hl8
            · intro h l hl hl8
              by_cases same : l=k.val
              · subst l
                exact good
              · exact h l (by omega) hl8
          unfold NCO_ParserRef.validate_ref_loop0_loop0
          rw [NCO_LoopSteps.loop_continue _ _ _ step]
          change NCO_ParserRef.validate_ref_loop0_loop0 payload i successor = _
          rw [recursive, propext suffix]
        · have notAll : ¬GoodFrom payload i.val k.val := by
            intro h
            exact good (h k.val (by omega) lt)
          rw [if_neg good] at step
          unfold NCO_ParserRef.validate_ref_loop0_loop0
          rw [NCO_LoopSteps.loop_done _ _ _ step, if_neg notAll]
  exact all (8-j.val) j hj rfl

#print axioms start
#print axioms run
end NCO_Inner
