import NMX_R8_EncodedFactor241
import NMS_R2N_RSLRanges
set_option autoImplicit false
noncomputable section
namespace NMX_R8_ProofSlice241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

theorem selected (data : Slice U8) (width : data.val.length = 58295) :
 ∃ proof, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  data ⟨688#usize,58295#usize⟩ = ok proof ∧
  NMS_R2N_RSLScalars.bytes proof = RSL.slice (NMS_R2N_RSLScalars.bytes data) 688 58295 := by
 have ordered : (688#usize).val ≤ (58295#usize).val := by scalar_tac
 have within : (58295#usize).val ≤ data.val.length := by rw [width]; scalar_tac
 obtain ⟨proof,run,_,_⟩ := WP.spec_imp_exists
  (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨688#usize,58295#usize⟩ data ordered within)
 refine ⟨proof,run,?_⟩
 have same := NMS_R2N_RSLRanges.selected data proof 688#usize 58295#usize ordered within run
 have start : (688#usize).val = 688 := by scalar_tac
 have finish : (58295#usize).val = 58295 := by scalar_tac
 simpa only [start,finish] using same
#print axioms selected
end NMX_R8_ProofSlice241
end
