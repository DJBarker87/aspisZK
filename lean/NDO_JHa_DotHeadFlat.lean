import NDO_JHa_DotContext
import NDO_JHa_DotHeadMeaning
import NDO_JHa_DotSumBlocks
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotHeadFlat
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem source (d : JHa_DotContext.Data) :
    ∃ out, JFs_TX2_ScalarHead.sourceCall d.q
      JFr_TX2_FirstLane.native (Usize.ofNat d.slot.val (by have:=d.slot.isLt;scalar_tac))=ok out ∧
      FIo_WideValues.Canon out ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=
        JHa_DotInnerMeaning.sum d j 0 26%2147483647 := by
  obtain ⟨out,run,canon,values⟩ := JHa_DotHeadMeaning.source d
  refine ⟨out,run,canon,?_⟩
  intro j
  rw [values j,JHa_DotSumBlocks.source d j 7 (by omega)]
  rfl
#print axioms source
end AspisR1.JHa_DotHeadFlat
end
