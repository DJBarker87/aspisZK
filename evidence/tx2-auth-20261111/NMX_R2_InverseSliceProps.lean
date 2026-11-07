import NMX_R2_InverseSlice
set_option autoImplicit false
namespace NMX_R2_InverseSliceProps
open Aeneas Aeneas.Std NMX_R2_Carrier NMX_R2_InverseBytes

theorem image (b : RSL.Bytes) (raw : Slice U8)
 (represented : NMX_R2_InverseSlice.fromBytes b = some raw) : bytes raw = b := by
 unfold NMX_R2_InverseSlice.fromBytes at represented
 split at represented
 · cases represented
   simp only [bytes,List.map_map,Function.comp_def,byte_roundtrip]
   change b.map id = b
   rw [List.map_id]
 · cases represented

theorem too_large (b : RSL.Bytes) (unrepresented : NMX_R2_InverseSlice.fromBytes b = none) :
 Usize.max < b.length := by
 unfold NMX_R2_InverseSlice.fromBytes at unrepresented
 split at unrepresented
 · cases unrepresented
 · omega

theorem lane_fits : (768 : Nat) ≤ Usize.max := by scalar_tac
#print axioms image
#print axioms too_large
#print axioms lane_fits
end NMX_R2_InverseSliceProps
