import NEO_WideWord
import NEO_ParserTotal
set_option autoImplicit false
namespace NEO_WideReference
open Aeneas Aeneas.Std Result AspisR1
attribute [local irreducible] core.num.U32.from_le_bytes

theorem fixed (bytes : Array U8 32#usize) :
 NEO_WindowV2.wide bytes.to_slice = NEO_ParserRef.limbs_ref (NBG_WideBytes.limbs bytes) := by
 have w0 := NEO_WideWord.fixed bytes 0#usize 0 (by decide) (by decide)
 have w1 := NEO_WideWord.fixed bytes 4#usize 1 (by decide) (by decide)
 have w2 := NEO_WideWord.fixed bytes 8#usize 2 (by decide) (by decide)
 have w3 := NEO_WideWord.fixed bytes 12#usize 3 (by decide) (by decide)
 have w4 := NEO_WideWord.fixed bytes 16#usize 4 (by decide) (by decide)
 have w5 := NEO_WideWord.fixed bytes 20#usize 5 (by decide) (by decide)
 have w6 := NEO_WideWord.fixed bytes 24#usize 6 (by decide) (by decide)
 have w7 := NEO_WideWord.fixed bytes 28#usize 7 (by decide) (by decide)
 simp [NEO_WindowV2.wide,Slice.len,Array.to_slice,bytes.property,w0,w1,w2,w3,w4,w5,w6,w7,
  NEO_WindowV2.P,NEO_ParserRef.limbs_ref,NEO_ParserRef.MODULUS,NBG_WideBytes.limbs,
  Array.index_usize,Array.make,bind_tc_ok]

theorem result (bytes : Array U8 32#usize) :
 NEO_WindowV2.wide bytes.to_slice =
 (do let parsed ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes.to_slice
     match parsed with
     | none => ok none
     | some value => do
       let words ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
       ok (some words)) := by
 rw [fixed,NEO_ParserTotal.result,←NBG_WideBytes.bytes_result]

#print axioms fixed
#print axioms result
end NEO_WideReference
