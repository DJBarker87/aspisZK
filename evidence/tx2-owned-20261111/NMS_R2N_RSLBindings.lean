import NMS_R2N_RSLScalars
set_option autoImplicit false
namespace NMS_R2N_RSLBindings
open AdapterRw NMS_R2N_RSLScalars
theorem b32_ext (a b : RSL.B32) (same : a.bytes = b.bytes) : a = b := by
 cases a
 cases b
 cases same
 rfl
#print axioms b32_ext

/-- Exact frozen private-leaf-salts profile/release bytes on the RSL carrier. -/
theorem profile : b32 r1_pool_adapter.PROFILE_BINDING = RSL.PROFILE_BINDING := by
 apply b32_ext
 unfold b32 r1_pool_adapter.PROFILE_BINDING RSL.PROFILE_BINDING RSL.mkB32
 decide

theorem release : b32 r1_pool_adapter.RELEASE_BINDING = RSL.RELEASE_BINDING := by
 apply b32_ext
 unfold b32 r1_pool_adapter.RELEASE_BINDING RSL.RELEASE_BINDING RSL.mkB32
 decide
#print axioms profile
#print axioms release
end NMS_R2N_RSLBindings
