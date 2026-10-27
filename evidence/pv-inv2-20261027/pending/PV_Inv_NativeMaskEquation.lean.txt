import R1Z.PV_Inv_MaskTable
import R1Z.PV_Inv_NativeRowsActive
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeMaskEquation
open R0P PV_Inv_RegistryInput
variable {K : Type} [Field K]

theorem rows_equation (registry : List (SourceLink K)) (enumeration : P_registry registry) :
    PV_Inv_NativeRowsActive.rows registry=PV_Inv_MaskSource.rows := by
  rw [PV_Inv_NativeRowsActive.rows,enumeration,List.flatMap_map]
  rfl

/-- The raw dynamic mask fold, after the actual enumerator/descriptor join.
The installed sorted/deduplicated implementation must preserve the row set;
MaskFold.order_irrelevant proves the independent finite-bit transport. -/
theorem source_equation (registry : List (SourceLink K)) (enumeration : P_registry registry)
    (block : Fin 64) :
    (PV_Inv_NativeRowsActive.rows registry).foldl
      (fun acc r => if r.val / 16=block.val then acc ||| (2^(r.val%16)) else acc) 0 =
      copyActiveRowMasks block := by
  rw [rows_equation registry enumeration]
  exact PV_Inv_MaskTable.source_equation block

#print axioms rows_equation
#print axioms source_equation
end R1Z.PV_Inv_NativeMaskEquation
