import PV_B3P_MaskIndexNative14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 PV_B3P_Success227
set_option autoImplicit false

theorem mask_source_subtraction_safe14 (mask : U16) (nonzero : mask ≠ 0#u16) :
    1 ≤ mask.val ∧ mask.val-1 < UScalar.size .U16 := by
  have positive : 0 < mask.val := by scalar_tac
  have bound := mask.hBounds
  constructor
  · omega
  · change mask.val-1 < 65536
    scalar_tac

theorem mask_source_read_success14 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (allowed : MaskAllowed mask) (index : Nat)
    (member : index ∈ PV_B3P_Mask227.walk 16 mask.val) :
    ∃ value, mask_read10 values index = .ok value := by
  have bound := mask_walk_indices14 mask allowed index member
  rw [mask_read_source_index14 values index bound]
  have b : (mask_index14 index bound).val < (16#usize).val := bound
  exact ⟨_,PV_B3P_SelectIndex227.index_value values (mask_index14 index bound) b⟩
#print axioms mask_source_subtraction_safe14
#print axioms mask_source_read_success14
end PV_B3P_Correct14227
