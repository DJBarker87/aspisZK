import NDB_ScanDecision
import NCV_ArrayRead
import NCV_Reference.Funs
set_option autoImplicit false
namespace NDB_DigestDecision
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def Same (a b : Array U32 8#usize) (j : Nat) : Prop :=
  NCV_ArrayFrame.coord a j=NCV_ArrayFrame.coord b j

theorem loop_value (a b : Array U32 8#usize) (i : Usize) (bound : i.val ≤ 8) :
    NCV_Reference.eq_digest_loop a b i=ok
      (if NDB_ScanDecision.Suffix (Same a b) 8 i.val then none else some false) := by
  classical
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.eq_digest_loop.body a b i=ok
        (if Same a b i.val then .cont next else .done (some false)) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have ra:=NCV_ArrayRead.read a i hi
    have rb:=NCV_ArrayRead.read b i hi
    refine ⟨next,value,?_⟩
    simp only [NCV_Reference.eq_digest_loop.body,lt,ite_true,ra,rb,bind_tc_ok,Same]
    by_cases test : NCV_ArrayFrame.coord a i.val=NCV_ArrayFrame.coord b i.val <;>
      simp [test,advance]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_Reference.eq_digest_loop.body a b i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_Reference.eq_digest_loop.body,no,ite_false]
  unfold NCV_Reference.eq_digest_loop
  exact NDB_ScanDecision.run _ (Same a b) 8 steps done i bound

theorem value (a b : Array U32 8#usize) :
    NCV_Reference.eq_digest a b=ok (decide (a=b)) := by
  classical
  have same : NDB_ScanDecision.Suffix (Same a b) 8 0 ↔ a=b := by
    constructor
    · intro h
      apply NCV_ArrayFrame.whole a b
      intro j hj hn
      exact h j (Nat.zero_le j) hj
    · intro h j _ _
      simp only [Same,h]
  unfold NCV_Reference.eq_digest
  rw [loop_value a b 0#usize (by scalar_tac)]
  simp only [show (0#usize).val=0 from rfl,propext same]
  by_cases h : a=b <;> simp only [h,ite_true,ite_false,bind_tc_ok,decide_true,decide_false]
#print axioms loop_value
#print axioms value
end NDB_DigestDecision
