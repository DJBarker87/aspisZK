import NDO_JHa_DotContext
import NDO_JHa_DotInnerMeaning
import RPt_JFv_TX2_FoldMeaning
import RPt_JFv_TX2_FoldValue
import RPt_JFs_TX2_OuterActive
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotOuterStepMeaning
open Aeneas Aeneas.Std Result ControlFlow
open JFv_TX2_ArrayMeaning (cell)

def batch (d : JHa_DotContext.Data) (j : Fin 8) (start : Nat) : Nat :=
  JFv_TX2_FoldValue.value (JHa_DotInnerMeaning.sum d j start (min (start+4) 26-start))

theorem source (d : JHa_DotContext.Data) (iter : JFs_TX2_Iterator.Iter)
    (limbs : Array U64 8#usize) (n : Nat) (hn : n<7)
    (step : iter.step_by.val=4) (finish : iter.iter.end.val=26)
    (active : iter.iter.start.val < iter.iter.end.val)
    (bound : JFs_TX2_FoldEight.Bound limbs n) :
    ∃ next out,
      FIp_NativeDots.fast_dots.four_dots_one_loop0.body
        d.q JFr_TX2_FirstLane.native
        (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac)) iter limbs=ok (cont (next,out)) ∧
      next.iter.start.val=min (iter.iter.start.val+4) 26 ∧ next.iter.end.val=26 ∧
      next.step_by.val=4 ∧ JFs_TX2_FoldEight.Bound out (n+1) ∧
      ∀ j : Fin 8, (cell out j).val=(cell limbs j).val+batch d j iter.iter.start.val := by
  obtain ⟨next,hi,inc,he,step'⟩ := JFs_TX2_Iterator.next iter step active
  obtain ⟨end4,stop,ha,hm,ordered,small,width,vs⟩ := JFs_TX2_BatchWindow.source iter.iter.start (by omega)
  obtain ⟨sums,hinner,_,innerValues⟩ := JHa_DotInnerMeaning.source d
    {start:=iter.iter.start,«end»:=stop} ordered small width
  obtain ⟨out,hfold,bo,foldValues⟩ := JFv_TX2_FoldMeaning.source sums limbs n hn bound
  refine ⟨next,out,?_,by simpa only [finish] using inc,by simpa only [he] using finish,step',bo,?_⟩
  · rw [JFs_TX2_OuterStep.body]
    simp only [JFs_TX2_OuterStep.step,hi,bind_tc_ok,Aeneas.Std.uncurry,ha,hm,hinner,hfold]
  · intro j
    rw [foldValues j,JFv_TX2_FoldValue.source,innerValues j]
    change (cell limbs j).val+JFv_TX2_FoldValue.value (JHa_DotInnerMeaning.sum d j iter.iter.start.val
      (stop.val-iter.iter.start.val))=_
    rw [vs]
    rfl
#print axioms source
end AspisR1.JHa_DotOuterStepMeaning
end
