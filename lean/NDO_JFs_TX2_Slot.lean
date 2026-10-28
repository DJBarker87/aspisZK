import NDO_JFs_TX2_TailTotal
import NDO_JFs_TX2_ScalarHead
import NDO_JFs_TX2_WideAdd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Slot
open Aeneas Aeneas.Std Result

theorem source (i : Fin 12) (slot : Fin 4) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one
      (JFr_TX2_Windows.array (JFn_Values.position i)) JFr_TX2_FirstLane.native
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨limbs,loop,_⟩ := JFs_TX2_Outer.source i slot
  obtain ⟨head,finish,ch⟩ := JFs_TX2_ScalarFinish.source limbs
  obtain ⟨tail,ht,ct⟩ := JFs_TX2_TailTotal.source i slot JFr_TX2_FirstLane.native
  obtain ⟨out,add,canon⟩ := JFs_TX2_WideAdd.source head tail ch ct
  refine ⟨out,?_,canon⟩
  rw [JFs_TX2_DotSuffix.body]
  simp only [JFs_TX2_Iterator.initial,bind_tc_ok,loop,finish,ht,add]

#print axioms source
end AspisR1.JFs_TX2_Slot
end
