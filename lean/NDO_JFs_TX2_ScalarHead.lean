import RPu_JFs_TX2_ScalarFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_ScalarHead
open Aeneas Aeneas.Std Result

def sourceCall (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Usize) : Result FIo_Install.NE := do
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    {start:=0#usize,«end»:=26#usize} 4#usize
  let limbs ← FIp_NativeDots.fast_dots.four_dots_one_loop0 iter q g slot (Array.repeat 8#usize 0#u64)
  JFs_TX2_DotSuffix.scalarFinish limbs

theorem source (i : Fin 12) (slot : Fin 4) :
    ∃ out, sourceCall (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨limbs,run,_⟩ := JFs_TX2_Outer.source i slot
  obtain ⟨out,finish,canon⟩ := JFs_TX2_ScalarFinish.source limbs
  exact ⟨out,by simp only [sourceCall,JFs_TX2_Iterator.initial,bind_tc_ok,run,finish],canon⟩

#print axioms source
end AspisR1.JFs_TX2_ScalarHead
end
