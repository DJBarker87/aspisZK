from pathlib import Path
E=Path(__file__).resolve().parent/'NDB_generated'
s='''import NDB_ScanDecision
import NCV_ArrayRead
import NCV_Reference.Funs
set_option autoImplicit false
namespace NDB_SequenceDecision
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
'''
for mode,condition,guard in [('valid','(NCV_ArrayFrame.coord seq j).val ≤ 1048576','NCV_ArrayFrame.coord seq i.val>1048576#u64'),('zero','NCV_ArrayFrame.coord seq j=0#u64','(NCV_ArrayFrame.coord seq i.val != 0#u64)=true')]:
 fname=mode+'_sequences';good='(fun j=>'+condition+')'
 s+=f'''
theorem {mode}_loop (seq : Array U64 8#usize) (i : Usize) (bound : i.val ≤ 8) :
    NCV_Reference.{fname}_loop seq i=ok
      (if NDB_ScanDecision.Suffix {good} 8 i.val then none else some false) := by
  classical
  have steps : ∀ i : Usize, i.val<8 → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.{fname}_loop.body seq i=ok
        (if {condition.replace(' j',' i.val')} then .cont next else .done (some false)) := by
    intro i hi
    obtain ⟨next,advance,value⟩:=NCV_Loop.advance i (by omega)
    have lt : i<8#usize := by scalar_tac
    have read:=NCV_ArrayRead.read seq i hi
    refine ⟨next,value,?_⟩
    by_cases test : {condition.replace(' j',' i.val')}
    · have guard : ¬({guard}) := by scalar_tac
      simp only [NCV_Reference.{fname}_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,advance,test,Bool.false_eq_true,show (0#u64 != 0#u64)=false from rfl]
    · have guard : {guard} := by scalar_tac
      simp only [NCV_Reference.{fname}_loop.body,lt,ite_true,read,bind_tc_ok,
        guard,ite_false,test]
  have done : ∀ i : Usize, 8 ≤ i.val → NCV_Reference.{fname}_loop.body seq i=ok (.done none) := by
    intro i hi
    have no : ¬i<8#usize := by scalar_tac
    simp only [NCV_Reference.{fname}_loop.body,no,ite_false]
  unfold NCV_Reference.{fname}_loop
  exact NDB_ScanDecision.run _ {good} 8 (by
    intro j hj
    obtain ⟨next,value,step⟩:=steps j hj
    refine ⟨next,value,?_⟩
    by_cases test : {condition.replace(' j',' j.val')} <;>
      simpa only [test,ite_true,ite_false] using step) done i bound

theorem {mode} (seq : Array U64 8#usize) :
    NCV_Reference.{fname} seq=ok (decide (NDB_ScanDecision.Suffix {good} 8 0)) := by
  classical
  unfold NCV_Reference.{fname}
  rw [{mode}_loop seq 0#usize (by scalar_tac)]
  by_cases good : NDB_ScanDecision.Suffix {good} 8 0 <;>
    simp only [show (0#usize).val=0 from rfl,good,ite_true,ite_false,bind_tc_ok,decide_true,decide_false]
#print axioms {mode}_loop
#print axioms {mode}
'''
s+='end NDB_SequenceDecision\n'
(E/'NDB_SequenceDecision.lean').write_text(s)
