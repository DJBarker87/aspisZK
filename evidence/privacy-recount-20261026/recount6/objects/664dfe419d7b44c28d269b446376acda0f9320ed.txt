import Aeneas
import R1Z.PV_CBL_FallbackBlock
import R1Z.PV_CBL_ShaBytes
import R1Z.PV_CBL_ShaPadFixed
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CBL_FinalSoft
def sha_length_suffix64 (w : Std.U64) : Result (Array Std.U8 8#usize) := do
  let i ← lift (Std.U64.wrapping_shr w 56#u32)
  let i1 ← lift (UScalar.cast .U8 i)
  let i2 ← lift (Std.U64.wrapping_shr w 48#u32)
  let i3 ← lift (UScalar.cast .U8 i2)
  let i4 ← lift (Std.U64.wrapping_shr w 40#u32)
  let i5 ← lift (UScalar.cast .U8 i4)
  let i6 ← lift (Std.U64.wrapping_shr w 32#u32)
  let i7 ← lift (UScalar.cast .U8 i6)
  let i8 ← lift (Std.U64.wrapping_shr w 24#u32)
  let i9 ← lift (UScalar.cast .U8 i8)
  let i10 ← lift (Std.U64.wrapping_shr w 16#u32)
  let i11 ← lift (UScalar.cast .U8 i10)
  let i12 ← lift (Std.U64.wrapping_shr w 8#u32)
  let i13 ← lift (UScalar.cast .U8 i12)
  let i14 ← lift (UScalar.cast .U8 w)
  ok (Array.make 8#usize [ i1, i3, i5, i7, i9, i11, i13, i14 ])

def sha_compress_byte_owned
  (state : Array Std.U32 8#usize) (block : Array Std.U8 64#usize) :
  Result (Array Std.U32 8#usize)
  := do
  let a ← PV_CBL_ShaBytes.sha_load64 block
  PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state a

def sha_digest32
  (state : Array Std.U32 8#usize) : Result (Array Std.U8 32#usize) := do
  let i ← Array.index_usize state 0#usize
  let a ← PV_CBL_ShaBytes.sha_store_be4 i
  let i1 ← Array.index_usize state 1#usize
  let b ← PV_CBL_ShaBytes.sha_store_be4 i1
  let i2 ← Array.index_usize state 2#usize
  let c ← PV_CBL_ShaBytes.sha_store_be4 i2
  let i3 ← Array.index_usize state 3#usize
  let d ← PV_CBL_ShaBytes.sha_store_be4 i3
  let i4 ← Array.index_usize state 4#usize
  let e ← PV_CBL_ShaBytes.sha_store_be4 i4
  let i5 ← Array.index_usize state 5#usize
  let f ← PV_CBL_ShaBytes.sha_store_be4 i5
  let i6 ← Array.index_usize state 6#usize
  let g ← PV_CBL_ShaBytes.sha_store_be4 i6
  let i7 ← Array.index_usize state 7#usize
  let h ← PV_CBL_ShaBytes.sha_store_be4 i7
  let i8 ← Array.index_usize a 0#usize
  let i9 ← Array.index_usize a 1#usize
  let i10 ← Array.index_usize a 2#usize
  let i11 ← Array.index_usize a 3#usize
  let i12 ← Array.index_usize b 0#usize
  let i13 ← Array.index_usize b 1#usize
  let i14 ← Array.index_usize b 2#usize
  let i15 ← Array.index_usize b 3#usize
  let i16 ← Array.index_usize c 0#usize
  let i17 ← Array.index_usize c 1#usize
  let i18 ← Array.index_usize c 2#usize
  let i19 ← Array.index_usize c 3#usize
  let i20 ← Array.index_usize d 0#usize
  let i21 ← Array.index_usize d 1#usize
  let i22 ← Array.index_usize d 2#usize
  let i23 ← Array.index_usize d 3#usize
  let i24 ← Array.index_usize e 0#usize
  let i25 ← Array.index_usize e 1#usize
  let i26 ← Array.index_usize e 2#usize
  let i27 ← Array.index_usize e 3#usize
  let i28 ← Array.index_usize f 0#usize
  let i29 ← Array.index_usize f 1#usize
  let i30 ← Array.index_usize f 2#usize
  let i31 ← Array.index_usize f 3#usize
  let i32 ← Array.index_usize g 0#usize
  let i33 ← Array.index_usize g 1#usize
  let i34 ← Array.index_usize g 2#usize
  let i35 ← Array.index_usize g 3#usize
  let i36 ← Array.index_usize h 0#usize
  let i37 ← Array.index_usize h 1#usize
  let i38 ← Array.index_usize h 2#usize
  let i39 ← Array.index_usize h 3#usize
  ok
    (Array.make 32#usize [
      i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22,
      i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33, i34, i35, i36,
      i37, i38, i39
      ])

def sha_finalize_soft_owned
  (state : Array Std.U32 8#usize) (blocks : Std.U64)
  (buffer : Array Std.U8 64#usize) (pos : Std.Usize) :
  Result ((Array Std.U8 32#usize) × (Array Std.U32 8#usize) × (Array Std.U8
    64#usize) × Std.Usize)
  := do
  let i ← lift (UScalar.cast .U64 pos)
  let i1 ← lift (core.num.U64.wrapping_mul 64#u64 blocks)
  let i2 ← lift (core.num.U64.wrapping_add i i1)
  let bits ← lift (core.num.U64.wrapping_mul 8#u64 i2)
  let a ← sha_length_suffix64 bits
  let (first, second, retained, newpos) ← PV_CBL_ShaPadFixed.sha_pad_owned_split8 buffer pos a
  let next ← sha_compress_byte_owned state first
  let next1 ←
    match second with
    | none => ok next
    | some block => sha_compress_byte_owned next block
  let a1 ← sha_digest32 next1
  ok (a1, next1, retained, newpos)

#print axioms sha_length_suffix64
#print axioms sha_compress_byte_owned
#print axioms sha_digest32
#print axioms sha_finalize_soft_owned
end PV_CBL_FinalSoft
