import NCV_ArrayRead
import NCV_ScanRun
import NCV_CastRef.Funs
set_option autoImplicit false
namespace NCV_SequenceValidation
open Aeneas Aeneas.Std Result

theorem valid (seq : Array U64 8#usize)
    (good : ∀ j, j<8 → (NCV_ArrayFrame.coord seq j).val ≤ 1048576) :
    NCV_CastRef.valid_sequences seq=ok true := by
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_CastRef.valid_sequences_loop.body seq i=ok (.cont next) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read seq i hi
    have bound:=good i.val hi
    have no : ¬NCV_ArrayFrame.coord seq i.val>1048576#u64 := by scalar_tac
    refine ⟨next,value,?_⟩
    simp only [NCV_CastRef.valid_sequences_loop.body,lt,ite_true,read,bind_tc_ok,no,ite_false,advance]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_CastRef.valid_sequences_loop.body seq i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_CastRef.valid_sequences_loop.body,no,ite_false]
  have call : NCV_CastRef.valid_sequences_loop seq 0#usize=ok none := by
    unfold NCV_CastRef.valid_sequences_loop
    exact NCV_ScanRun.run_none _ 8 steps done _ (by scalar_tac)
  simp only [NCV_CastRef.valid_sequences,call,bind_tc_ok]

theorem zero (seq : Array U64 8#usize)
    (good : ∀ j, j<8 → NCV_ArrayFrame.coord seq j=0#u64) :
    NCV_CastRef.zero_sequences seq=ok true := by
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_CastRef.zero_sequences_loop.body seq i=ok (.cont next) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read seq i hi
    refine ⟨next,value,?_⟩
    have z : (0#u64 != 0#u64)=false := rfl
    simp only [NCV_CastRef.zero_sequences_loop.body,lt,ite_true,read,bind_tc_ok,good i.val hi,z,Bool.false_eq_true,ite_false,advance]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_CastRef.zero_sequences_loop.body seq i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_CastRef.zero_sequences_loop.body,no,ite_false]
  have call : NCV_CastRef.zero_sequences_loop seq 0#usize=ok none := by
    unfold NCV_CastRef.zero_sequences_loop
    exact NCV_ScanRun.run_none _ 8 steps done _ (by scalar_tac)
  simp only [NCV_CastRef.zero_sequences,call,bind_tc_ok]

#print axioms valid
#print axioms zero
end NCV_SequenceValidation
