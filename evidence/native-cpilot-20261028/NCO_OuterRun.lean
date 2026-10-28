import NCO_Outer
import NCO_Search
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_OuterRun
attribute [local instance] Classical.propDecidable

noncomputable def bad (payload : Slice U8) (i : Nat) : Bool :=
  decide (¬NCO_Inner.GoodFrom payload i 0)

def Outcome (payload : Slice U8) (start : Nat) (final : Usize)
    (pending : Option (core.result.Result Unit NCO_ParserRef.RefError)) : Prop :=
  match NCO_Search.search (bad payload) (payload.val.length/32) start with
  | none => final.val=payload.val.length/32 ∧ pending=some (.Ok ())
  | some i => final.val=i ∧ pending=none

theorem run (payload : Slice U8) (i : Usize) (cap : payload.val.length ≤ 3712)
    (bound : i.val ≤ payload.val.length/32) :
    ∃ final pending, NCO_ParserRef.validate_ref_loop0 payload i=ok (final,pending) ∧
      Outcome payload i.val final pending := by
  have all : ∀ n : Nat, ∀ j : Usize, j.val ≤ payload.val.length/32 →
      payload.val.length/32-j.val=n →
      ∃ final pending, NCO_ParserRef.validate_ref_loop0 payload j=ok (final,pending) ∧
        Outcome payload j.val final pending := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj hn
      by_cases terminal : payload.val.length/32 ≤ j.val
      · refine ⟨j,some (.Ok ()),?_,?_⟩
        · unfold NCO_ParserRef.validate_ref_loop0
          exact NCO_LoopSteps.loop_done _ _ _ (NCO_Outer.done payload j terminal)
        · unfold Outcome
          rw [NCO_Search.terminal _ _ _ terminal]
          exact ⟨by omega,rfl⟩
      · have lt : j.val < payload.val.length/32 := by omega
        obtain ⟨successor,value,step⟩ := NCO_Outer.step payload j cap lt
        by_cases good : NCO_Inner.GoodFrom payload j.val 0
        · rw [if_pos good] at step
          obtain ⟨final,pending,call,outcome⟩ :=
            ih (payload.val.length/32-successor.val) (by omega) successor (by omega) rfl
          refine ⟨final,pending,?_,?_⟩
          · unfold NCO_ParserRef.validate_ref_loop0
            rw [NCO_LoopSteps.loop_continue _ _ _ step]
            exact call
          · have search : NCO_Search.search (bad payload) (payload.val.length/32) j.val =
                NCO_Search.search (bad payload) (payload.val.length/32) successor.val := by
              rw [NCO_Search.step _ _ _ lt]
              simp only [bad,good,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,value]
            simpa only [Outcome,search] using outcome
        · have search : NCO_Search.search (bad payload) (payload.val.length/32) j.val = some j.val := by
            rw [NCO_Search.step _ _ _ lt]
            simp [bad,good]
          rw [if_neg good] at step
          refine ⟨j,none,?_,?_⟩
          · unfold NCO_ParserRef.validate_ref_loop0
            exact NCO_LoopSteps.loop_done _ _ _ step
          · simp [Outcome,search]
  exact all (payload.val.length/32-i.val) i bound rfl

#print axioms run
end NCO_OuterRun
