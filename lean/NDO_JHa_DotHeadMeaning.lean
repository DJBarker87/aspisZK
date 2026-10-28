import NDO_JHa_DotContext
import NDO_JHa_DotOuterMeaning
import RPu_JFv_TX2_ScalarMeaning
import NDO_JFs_TX2_ScalarHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotHeadMeaning
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem source (d : JHa_DotContext.Data) :
    ∃ out, JFs_TX2_ScalarHead.sourceCall d.q
      JFr_TX2_FirstLane.native (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac))=ok out ∧
      FIo_WideValues.Canon out ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=JHa_DotOuterMeaning.sum d j 7%2147483647 := by
  obtain ⟨limbs,run,_,values⟩ := JHa_DotOuterMeaning.source d
  obtain ⟨out,finish,canon,finalValues⟩ := JFv_TX2_ScalarMeaning.source limbs
  refine ⟨out,?_,canon,?_⟩
  · simp only [JFs_TX2_ScalarHead.sourceCall,JFs_TX2_Iterator.initial,bind_tc_ok,run,finish]
  · intro j
    rw [finalValues j,values j]
#print axioms source
end AspisR1.JHa_DotHeadMeaning
end
