import R1Z.PV_CBL_ByteCodecValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteStoreRead
set_option autoImplicit false
theorem read0 (w : U32) : Array.index_usize (PV_CBL_ByteCodecValue.store w) 0#usize =
    ok (UScalar.cast .U8 (U32.wrapping_shr w 24#u32)) := by
  simp [PV_CBL_ByteCodecValue.store,Array.index_usize,Array.getElem?_Usize_eq,Array.make]
theorem read1 (w : U32) : Array.index_usize (PV_CBL_ByteCodecValue.store w) 1#usize =
    ok (UScalar.cast .U8 (U32.wrapping_shr w 16#u32)) := by
  simp [PV_CBL_ByteCodecValue.store,Array.index_usize,Array.getElem?_Usize_eq,Array.make]
theorem read2 (w : U32) : Array.index_usize (PV_CBL_ByteCodecValue.store w) 2#usize =
    ok (UScalar.cast .U8 (U32.wrapping_shr w 8#u32)) := by
  simp [PV_CBL_ByteCodecValue.store,Array.index_usize,Array.getElem?_Usize_eq,Array.make]
theorem read3 (w : U32) : Array.index_usize (PV_CBL_ByteCodecValue.store w) 3#usize =
    ok (UScalar.cast .U8 w) := by
  simp [PV_CBL_ByteCodecValue.store,Array.index_usize,Array.getElem?_Usize_eq,Array.make]
#print axioms read0
#print axioms read1
#print axioms read2
#print axioms read3
end R1Z.PV_CBL_ByteStoreRead
