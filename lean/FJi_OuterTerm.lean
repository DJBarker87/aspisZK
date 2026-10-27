import FJi_InnerValue
import JFv_TX2_FoldMeaning
import JFv_TX2_FoldValue
import JFs_TX2_OuterActive
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_OuterTerm
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations
open FJf_U64Array (cell)
abbrev Iter := JFs_TX2_Iterator.Iter

def batch (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (j start : Nat) : Nat := JFv_TX2_FoldValue.value
      (FJi_InnerStep.sum q g slot j start (min (start+4) 26-start))

theorem at_fin (a : Sums) (j : Fin 8) : cell a j.val=JFv_TX2_ArrayMeaning.cell a j := by
  unfold cell JFv_TX2_ArrayMeaning.cell
  rw [List.getElem?_eq_getElem (by rw [a.property];exact j.isLt)]
  rfl

/-- One actual outer group, including the two-term final group, on SAME q/g. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : Iter) (limbs : Sums) (n : Nat) (hn : n < 7)
    (step : iter.step_by.val=4) (finish : iter.iter.end.val=26)
    (active : iter.iter.start.val < iter.iter.end.val)
    (bound : JFs_TX2_FoldEight.Bound limbs n)
    (out : ControlFlow (Iter × Sums) Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0.body q g slot iter limbs=ok out) :
    ∃ next result, out=.cont (next,result) ∧
      next.iter.start.val=min (iter.iter.start.val+4) 26 ∧ next.iter.end.val=26 ∧
      next.step_by.val=4 ∧ JFs_TX2_FoldEight.Bound result (n+1) ∧
      ∀ j : Fin 8,(cell result j.val).val=(cell limbs j.val).val+batch q g slot j.val iter.iter.start.val := by
  obtain ⟨next,hi,inc,he,step'⟩ := JFs_TX2_Iterator.next iter step active
  obtain ⟨end4,stop,ha,hm,ordered,small,width,vs⟩ := JFs_TX2_BatchWindow.source iter.iter.start (by omega)
  rw [JFs_TX2_OuterStep.body] at run
  simp only [JFs_TX2_OuterStep.step,hi,bind_tc_ok,Aeneas.Std.uncurry,ha,hm] at run
  obtain ⟨sums,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨result,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨result',hr',bo,vo⟩ := JFv_TX2_FoldMeaning.source sums limbs n hn bound
  have same := Result.ok.inj (hr.symm.trans hr')
  subst result'
  refine ⟨next,result,(Result.ok.inj run).symm,by simpa only [finish] using inc,
    by simpa only [he] using finish,step',bo,?_⟩
  intro j
  rw [at_fin,vo j,←at_fin,←at_fin,JFv_TX2_FoldValue.source,
    FJi_InnerValue.group q g slot {start:=iter.iter.start,«end»:=stop} sums ordered small hs j.val j.isLt]
  change (cell limbs j.val).val+JFv_TX2_FoldValue.value
    (FJi_InnerStep.sum q g slot j.val iter.iter.start.val (stop.val-iter.iter.start.val))=_
  rw [vs]
  rfl
#print axioms at_fin
#print axioms value
end AspisR1.FJi_OuterTerm
end
