import NDB_ScanDecision
import NCV_ArrayRead
import NCV_Reference.Funs
set_option autoImplicit false
namespace NDB_SequenceDecision
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem valid_loop (seq : Array U64 8#usize) (i : Usize) (bound : i.val ≤ 8) :
    NCV_Reference.valid_sequences_loop seq i=ok
      (if NDB_ScanDecision.Suffix (fun j=>(NCV_ArrayFrame.coord seq j).val ≤ 1048576) 8 i.val then none else some false) := by
  classical
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.valid_sequences_loop.body seq i=ok
        (if (NCV_ArrayFrame.coord seq i.val).val ≤ 1048576 then .cont next else .done (some false)) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read seq i hi
    refine ⟨next,value,?_⟩
    by_cases test : (NCV_ArrayFrame.coord seq i.val).val ≤ 1048576
    · have guard : ¬(NCV_ArrayFrame.coord seq i.val>1048576#u64) := by scalar_tac
      simp only [NCV_Reference.valid_sequences_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,advance,test]
    · have guard : NCV_ArrayFrame.coord seq i.val>1048576#u64 := by scalar_tac
      simp only [NCV_Reference.valid_sequences_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,test]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_Reference.valid_sequences_loop.body seq i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_Reference.valid_sequences_loop.body,no,ite_false]
  unfold NCV_Reference.valid_sequences_loop
  exact NDB_ScanDecision.run _ (fun j=>(NCV_ArrayFrame.coord seq j).val ≤ 1048576) 8 steps done i bound

theorem valid (seq : Array U64 8#usize) :
    NCV_Reference.valid_sequences seq=ok (decide (NDB_ScanDecision.Suffix (fun j=>(NCV_ArrayFrame.coord seq j).val ≤ 1048576) 8 0)) := by
  classical
  unfold NCV_Reference.valid_sequences
  rw [valid_loop seq 0#usize (by scalar_tac)]
  by_cases good : NDB_ScanDecision.Suffix (fun j=>(NCV_ArrayFrame.coord seq j).val ≤ 1048576) 8 0 <;>
    simp only [show (0#usize).val=0 from rfl,good,ite_true,ite_false,bind_tc_ok,decide_true,decide_false]
#print axioms valid_loop
#print axioms valid

theorem zero_loop (seq : Array U64 8#usize) (i : Usize) (bound : i.val ≤ 8) :
    NCV_Reference.zero_sequences_loop seq i=ok
      (if NDB_ScanDecision.Suffix (fun j=>NCV_ArrayFrame.coord seq j=0#u64) 8 i.val then none else some false) := by
  classical
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.zero_sequences_loop.body seq i=ok
        (if NCV_ArrayFrame.coord seq i.val=0#u64 then .cont next else .done (some false)) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read seq i hi
    refine ⟨next,value,?_⟩
    by_cases test : NCV_ArrayFrame.coord seq i.val=0#u64
    · have guard : ¬((NCV_ArrayFrame.coord seq i.val != 0#u64)=true) := by scalar_tac
      simp only [NCV_Reference.zero_sequences_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,advance,test]
    · have guard : (NCV_ArrayFrame.coord seq i.val != 0#u64)=true := by scalar_tac
      simp only [NCV_Reference.zero_sequences_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,test]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_Reference.zero_sequences_loop.body seq i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_Reference.zero_sequences_loop.body,no,ite_false]
  unfold NCV_Reference.zero_sequences_loop
  exact NDB_ScanDecision.run _ (fun j=>NCV_ArrayFrame.coord seq j=0#u64) 8 steps done i bound

theorem zero (seq : Array U64 8#usize) :
    NCV_Reference.zero_sequences seq=ok (decide (NDB_ScanDecision.Suffix (fun j=>NCV_ArrayFrame.coord seq j=0#u64) 8 0)) := by
  classical
  unfold NCV_Reference.zero_sequences
  rw [zero_loop seq 0#usize (by scalar_tac)]
  by_cases good : NDB_ScanDecision.Suffix (fun j=>NCV_ArrayFrame.coord seq j=0#u64) 8 0 <;>
    simp only [show (0#usize).val=0 from rfl,good,ite_true,ite_false,bind_tc_ok,decide_true,decide_false]
#print axioms zero_loop
#print axioms zero
end NDB_SequenceDecision
