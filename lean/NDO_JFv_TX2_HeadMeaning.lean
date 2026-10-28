import NDO_JFv_TX2_OuterMeaning
import RPu_JFv_TX2_ScalarMeaning
import NDO_JFs_TX2_ScalarHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_HeadMeaning
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem source (i : Fin 12) (slot : Fin 4) :
    ∃ out, JFs_TX2_ScalarHead.sourceCall (JFr_TX2_Windows.array (JFn_Values.position i))
      JFr_TX2_FirstLane.native (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧
      FIo_WideValues.Canon out ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=JFv_TX2_OuterMeaning.sum i slot j 7%2147483647 := by
  obtain ⟨limbs,run,_,values⟩ := JFv_TX2_OuterMeaning.source i slot
  obtain ⟨out,finish,canon,finalValues⟩ := JFv_TX2_ScalarMeaning.source limbs
  refine ⟨out,?_,canon,?_⟩
  · simp only [JFs_TX2_ScalarHead.sourceCall,JFs_TX2_Iterator.initial,bind_tc_ok,run,finish]
  · intro j
    rw [finalValues j,values j]
#print axioms source
end AspisR1.JFv_TX2_HeadMeaning
end
