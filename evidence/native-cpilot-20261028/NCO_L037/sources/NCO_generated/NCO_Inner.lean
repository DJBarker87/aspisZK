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

#print axioms start
end NCO_Inner
