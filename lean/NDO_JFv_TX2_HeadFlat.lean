import NDO_JFv_TX2_HeadMeaning
import NDO_JFv_TX2_SumBlocks
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_HeadFlat
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)

theorem source (i : Fin 12) (slot : Fin 4) :
    ∃ out, JFs_TX2_ScalarHead.sourceCall (JFr_TX2_Windows.array (JFn_Values.position i))
      JFr_TX2_FirstLane.native (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧
      FIo_WideValues.Canon out ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=
        JFv_TX2_InnerMeaning.sum i slot j 0 26%2147483647 := by
  obtain ⟨out,run,canon,values⟩ := JFv_TX2_HeadMeaning.source i slot
  refine ⟨out,run,canon,?_⟩
  intro j
  rw [values j,JFv_TX2_SumBlocks.source i slot j 7 (by omega)]
  rfl
#print axioms source
end AspisR1.JFv_TX2_HeadFlat
end
