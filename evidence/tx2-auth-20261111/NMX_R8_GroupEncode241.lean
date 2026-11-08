import NMX_R8_Children241
import NMX_R8_Factor241
import NMX_R8_OldFactor241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_GroupEncode241
open Aeneas Aeneas.Std Result AdapterRw

theorem source (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (val : r1_pool_adapter.ValidatedAsqa) (proof checkpoint : Slice U8)
 (start finish : Usize) (encoded : Array U8 1880#usize) :
 NMX_R8_OldFactor241.afterEncode ops (NMX_R8_Children241.original choices) val proof checkpoint start finish encoded =
 NMX_R8_Factor241.afterEncode ops (NMX_R8_Children241.grouped choices) val proof checkpoint start finish encoded := by
 unfold NMX_R8_OldFactor241.afterEncode NMX_R8_Factor241.afterEncode NMX_R8_Children241.original
 rfl
#print axioms source
end NMX_R8_GroupEncode241
end
