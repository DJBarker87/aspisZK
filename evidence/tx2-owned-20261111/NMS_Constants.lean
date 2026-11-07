import NMS_EmittedGetter
set_option autoImplicit false
namespace NMS_Constants
open Aeneas Aeneas.Std AdapterRw
def profile : Array Std.U8 32#usize :=
  Array.make 32#usize [
    87#u8, 148#u8, 115#u8, 19#u8, 210#u8, 50#u8, 100#u8, 26#u8, 216#u8, 21#u8,
    125#u8, 102#u8, 191#u8, 175#u8, 250#u8, 177#u8, 30#u8, 76#u8, 58#u8,
    153#u8, 51#u8, 29#u8, 24#u8, 244#u8, 75#u8, 250#u8, 202#u8, 182#u8, 137#u8,
    151#u8, 55#u8, 211#u8
    ]

theorem profile_eq : profile = r1_pool_adapter.PROFILE_BINDING := by
 unfold profile r1_pool_adapter.PROFILE_BINDING
 rfl
#print axioms profile_eq
def release : Array Std.U8 32#usize :=
  Array.make 32#usize [
    226#u8, 148#u8, 175#u8, 188#u8, 20#u8, 239#u8, 106#u8, 254#u8, 118#u8,
    184#u8, 71#u8, 222#u8, 244#u8, 68#u8, 82#u8, 248#u8, 76#u8, 195#u8, 114#u8,
    128#u8, 100#u8, 101#u8, 118#u8, 7#u8, 181#u8, 68#u8, 165#u8, 57#u8, 202#u8,
    155#u8, 50#u8, 58#u8
    ]

theorem release_eq : release = r1_pool_adapter.RELEASE_BINDING := by
 unfold release r1_pool_adapter.RELEASE_BINDING
 rfl
#print axioms release_eq
end NMS_Constants
