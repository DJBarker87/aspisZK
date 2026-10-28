import NDO_JGw_DotOuter
import NDO_JGw_DotTail
import RPu_JFs_TX2_ScalarFinish
import NDO_JFs_TX2_WideAdd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_DotTotal
open Aeneas Aeneas.Std Result

theorem source (q : Array U8 608#usize) (slot : Fin 4)
    (scalars : Fin 26 → U32)
    (reads : ∀ term, JFr_TX2_ScalarRead.read q
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))=ok (scalars term))
    (canonical : ∀ term, (scalars term).val<2147483647)
    (q0 q1 q2 : JFr_TX2_TailRead.Q)
    (hq0 : JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 0) (JFr_TX2_Tails.stop slot 0)=ok q0)
    (hq1 : JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 1) (JFr_TX2_Tails.stop slot 1)=ok q1)
    (hq2 : JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 2) (JFr_TX2_Tails.stop slot 2)=ok q2) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one q JFr_TX2_FirstLane.native
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨limbs,loop,_⟩ := JGw_DotOuter.source q slot scalars reads canonical
  obtain ⟨head,finish,ch⟩ := JFs_TX2_ScalarFinish.source limbs
  obtain ⟨tail,ht,ct⟩ := JGw_DotTail.source q slot q0 q1 q2 hq0 hq1 hq2 JFr_TX2_FirstLane.native
  obtain ⟨out,add,canon⟩ := JFs_TX2_WideAdd.source head tail ch ct
  refine ⟨out,?_,canon⟩
  rw [JFs_TX2_DotSuffix.body]
  simp only [JFs_TX2_Iterator.initial,bind_tc_ok,loop,finish,ht,add]
#print axioms source
end AspisR1.JGw_DotTotal
end
