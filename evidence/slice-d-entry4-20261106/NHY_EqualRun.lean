import NHY_EqualStep
set_option autoImplicit false
namespace NHY_EqualRun
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def SameFrom (b v : Slice U8) (start : Nat) : Prop :=
  ∀ j, start ≤ j → j < b.val.length → NHY_ZeroStep.byte b j=NHY_ZeroStep.byte v j

theorem run (b v : Slice U8) (i : Usize) (cap : b.val.length ≤ 768)
    (length : b.val.length=v.val.length) (bound : i.val ≤ b.val.length) :
    NCX_Reference.equal_loop b v i =
      ok (if SameFrom b v i.val then none else some false) := by
  classical
  have all : ∀ n : Nat, ∀ k : Usize, k.val ≤ b.val.length → b.val.length-k.val=n →
      NCX_Reference.equal_loop b v k=ok (if SameFrom b v k.val then none else some false) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk hn
      by_cases terminal : b.val.length ≤ k.val
      · have good : SameFrom b v k.val := by intro j hj hb;omega
        unfold NCX_Reference.equal_loop
        rw [NHY_ZeroLoop.done _ _ _ (NHY_EqualStep.terminal b v k terminal),if_pos good]
      · have lt : k.val < b.val.length := by omega
        obtain ⟨next,value,step⟩ := NHY_EqualStep.step b v k cap length lt
        by_cases good : NHY_ZeroStep.byte b k.val=NHY_ZeroStep.byte v k.val
        · rw [if_neg (not_not.mpr good)] at step
          have recursive := ih (b.val.length-next.val) (by omega) next (by omega) rfl
          have suffix : SameFrom b v k.val ↔ SameFrom b v next.val := by
            constructor
            · intro h j hj hb;exact h j (by omega) hb
            · intro h j hj hb
              by_cases same : j=k.val
              · simpa only [same] using good
              · exact h j (by omega) hb
          unfold NCX_Reference.equal_loop
          rw [NHY_ZeroLoop.cont _ _ _ step]
          change NCX_Reference.equal_loop b v next = _
          rw [recursive,propext suffix]
        · rw [if_pos good] at step
          have bad : ¬SameFrom b v k.val := by intro h;exact good (h k.val (by omega) lt)
          unfold NCX_Reference.equal_loop
          rw [NHY_ZeroLoop.done _ _ _ step,if_neg bad]
  exact all (b.val.length-i.val) i bound rfl

#print axioms run
end NHY_EqualRun
