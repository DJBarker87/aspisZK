import AspisR1SelectedMaskProbe.ActiveMaskBasisSourceSlice
import CopyActiveMaskBasisRegroup

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof

abbrev QM := field.QM31

def sourceMask (i : Fin 64) : Std.U16 :=
  pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS.val[i.val]'(by
    simpa [pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS] using i.isLt)

theorem source_mask_table (i : Fin 64) :
    (sourceMask i).val = R0P.copyActiveRowMasks i := by
  unfold sourceMask pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS
    R0P.copyActiveRowMasks
  fin_cases i <;> decide

#print axioms source_mask_table
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof
