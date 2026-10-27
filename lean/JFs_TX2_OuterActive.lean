import JFs_TX2_OuterStep
import JFs_TX2_BatchWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_OuterActive
open Aeneas Aeneas.Std Result ControlFlow

theorem source (i : Fin 12) (slot : Fin 4) (iter : JFs_TX2_Iterator.Iter)
    (limbs : Array U64 8#usize) (n : Nat) (hn : n<7)
    (step : iter.step_by.val=4) (finish : iter.iter.end.val=26)
    (active : iter.iter.start.val < iter.iter.end.val)
    (bound : JFs_TX2_FoldEight.Bound limbs n) :
    ∃ next out,
      FIp_NativeDots.fast_dots.four_dots_one_loop0.body
        (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) iter limbs=ok (cont (next,out)) ∧
      next.iter.start.val=min (iter.iter.start.val+4) 26 ∧ next.iter.end.val=26 ∧
      next.step_by.val=4 ∧ JFs_TX2_FoldEight.Bound out (n+1) := by
  obtain ⟨next,hi,inc,he,step'⟩ := JFs_TX2_Iterator.next iter step active
  obtain ⟨end4,stop,ha,hm,ordered,small,width,vs⟩ := JFs_TX2_BatchWindow.source iter.iter.start (by omega)
  obtain ⟨sums,hinner,_⟩ := JFs_TX2_Inner.source i slot {start:=iter.iter.start,«end»:=stop}
    (Array.repeat 8#usize 0#u64) iter.iter.start.val (by rfl) ordered small width
    (by simpa only [Nat.sub_self] using JFs_TX2_BatchWindow.zero)
  obtain ⟨out,hfold,bo⟩ := JFs_TX2_FoldEight.source sums limbs n hn bound
  refine ⟨next,out,?_,by simpa only [finish] using inc,by simpa only [he] using finish,step',bo⟩
  rw [JFs_TX2_OuterStep.body]
  simp only [JFs_TX2_OuterStep.step,hi,bind_tc_ok,Aeneas.Std.uncurry,ha,hm,hinner,hfold]

#print axioms source
end AspisR1.JFs_TX2_OuterActive
end
