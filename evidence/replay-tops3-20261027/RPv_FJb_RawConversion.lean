import RPv_FJa_PoseidonPow5
import RPv_FIw_PackArithmetic
import RPv_RawPoseidonExtensionWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_RawConversion
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm cm)
open FIv_Map (map map_bind map_ok)
theorem reduce (x : U64) : field.M31.reduce_u62 x=
    AspisR1SelectedMaskProbe.field.M31.reduce_u62 x := by
  simp only [field.M31.reduce_u62,AspisR1SelectedMaskProbe.field.M31.reduce_u62,
    field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    field.P,AspisR1SelectedMaskProbe.field.P]
theorem limbs (x : NQ) : state_only_poseidon.extension_limbs x=
    AspisR1SelectedMaskProbe.state_only_poseidon.extension_limbs (qm x) := rfl
theorem converted (xs : Array U64 4#usize) :
    map qm (state_only_poseidon.extension_from_raw_limbs xs)=
    AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs xs := by
  simp only [state_only_poseidon.extension_from_raw_limbs,
    AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs,
    reduce,←FIw_PackArithmetic.cm_new,FIv_NativeArithmetic.bind_map,map_bind,map_ok,qm,cm]
#print axioms reduce
#print axioms limbs
#print axioms converted
end AspisR1.FJb_RawConversion
end
