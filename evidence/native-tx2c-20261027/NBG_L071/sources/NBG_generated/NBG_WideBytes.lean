import NBG_WideCarriers
set_option autoImplicit false
noncomputable section
namespace NBG_WideBytes
open Aeneas Aeneas.Std Result
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def word (bytes : Array U8 32#usize) (i : Nat) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize
    [bytes.val[4*i]!,bytes.val[4*i+1]!,bytes.val[4*i+2]!,bytes.val[4*i+3]!])

def limbs (bytes : Array U8 32#usize) : Array U32 8#usize :=
  Array.make 8#usize [word bytes 0,word bytes 1,word bytes 2,word bytes 3,
    word bytes 4,word bytes 5,word bytes 6,word bytes 7]

/-- Every input byte is retained in the correct little-endian word. Rejection
and successful carriers are then exactly NBG_WideCarriers.limbs_result. -/
theorem bytes_result (bytes : Array U8 32#usize) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes.to_slice =
      FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (limbs bytes) := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    Slice.index_usize,Array.to_slice,Slice.len,Slice.length,bytes.property,
    limbs,word,lift,bind_tc_ok]

#print axioms bytes_result
end NBG_WideBytes
