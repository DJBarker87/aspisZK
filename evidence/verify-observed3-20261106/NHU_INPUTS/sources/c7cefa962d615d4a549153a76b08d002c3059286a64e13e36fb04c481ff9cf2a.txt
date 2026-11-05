import RPv_FIx_PreweightedPack
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std
namespace AspisR1.NHU_SharedPacking
open FIv_NativeValue (K)
/-- Optimized same-selector packing law for the SAME four ordered operands.
This is algebraic support; it is not an emitted optimized helper definition. -/
theorem factor (s : K) (v : Fin (4#usize).val→K) :
 FIx_PreweightedPack.pack (fun j=>s*v j)=s*FIx_PreweightedPack.pack v := by
 unfold FIx_PreweightedPack.pack
 ring
#print axioms factor
end AspisR1.NHU_SharedPacking
end
