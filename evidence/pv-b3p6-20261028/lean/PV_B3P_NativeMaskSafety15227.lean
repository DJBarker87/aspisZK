import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
import PV_B3P_MaskIndexNative14227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

open PV_B3P_Correct14227 PV_B3P_Success227

theorem native_mask_subtraction_safe15 (mask : U16) (nonzero : mask ≠ 0#u16) :
    1 ≤ mask.val ∧ mask.val-1 < UScalar.size .U16 := by
  have positive : 0 < mask.val := by scalar_tac
  have bound : mask.val < UScalar.size .U16 := by
    simpa only [UScalar.size] using mask.hBounds
  omega

theorem native_mask_read_success15 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (allowed : MaskAllowed mask) (index : Nat)
    (member : index ∈ PV_B3P_Mask227.walk 16 mask.val) :
    ∃ value, mask_read10 values index = .ok value := by
  have bound := mask_walk_indices14 mask allowed index member
  rw [mask_read_source_index14 values index bound]
  exact ⟨_,PV_B3P_SelectIndex227.index_value values (mask_index14 index bound) bound⟩
#print axioms native_mask_subtraction_safe15
#print axioms native_mask_read_success15
end PV_B3P_Native15227
