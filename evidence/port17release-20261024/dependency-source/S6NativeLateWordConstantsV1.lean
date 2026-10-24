import S6NativeLateWordCastV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6NativeLateWordCast

theorem word16_32 (raw : Array U8 2#usize)
    (guard : ¬(UScalar.cast .Usize (core.num.U16.from_le_bytes raw) != 32#usize)=true) :
    core.num.U16.to_le_bytes 32#u16=raw := by
  have cast_value : UScalar.cast .Usize 32#u16=32#usize := by scalar_tac
  apply word16_frame
  simpa only [cast_value] using guard

#print axioms word16_32
theorem word32_800 (raw : Array U8 4#usize)
    (guard : ¬(UScalar.cast .Usize (core.num.U32.from_le_bytes raw) != 800#usize)=true) :
    core.num.U32.to_le_bytes 800#u32=raw := by
  have cast_value : UScalar.cast .Usize 800#u32=800#usize := by scalar_tac
  apply word32_frame
  simpa only [cast_value] using guard

#print axioms word32_800
theorem word32_688 (raw : Array U8 4#usize)
    (guard : ¬(UScalar.cast .Usize (core.num.U32.from_le_bytes raw) != 688#usize)=true) :
    core.num.U32.to_le_bytes 688#u32=raw := by
  have cast_value : UScalar.cast .Usize 688#u32=688#usize := by scalar_tac
  apply word32_frame
  simpa only [cast_value] using guard

#print axioms word32_688
theorem word32_1520 (raw : Array U8 4#usize)
    (guard : ¬(UScalar.cast .Usize (core.num.U32.from_le_bytes raw) != 1520#usize)=true) :
    core.num.U32.to_le_bytes 1520#u32=raw := by
  have cast_value : UScalar.cast .Usize 1520#u32=1520#usize := by scalar_tac
  apply word32_frame
  simpa only [cast_value] using guard

#print axioms word32_1520
end AspisS6NativeLateWordCast
