import NDB_PrimaryWords
import NMX_R3_ByteWord
import NMX_R3_RawWord32
set_option autoImplicit false
namespace NMX_R3_Word32
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier
/-- Four-byte decoding at the exact canonical carrier, using only named
symbolic wrapper and bit-position laws. -/
theorem fixed (a b c d : U8) :
    word (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) =
      RSL.le32 (byte a) (byte b) (byte c) (byte d) := by
  have widen (x : U8) : (byte x).toUInt32 = (⟨x.bv.setWidth 32⟩ : UInt32) :=
    UInt32.toBitVec_inj.mp (NMX_R3_ByteWord.bits x)
  apply UInt32.toBitVec_inj.mp
  rw [NMX_R3_Bits.word_bits]
  change BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv] =
    (RSL.le32 (byte a) (byte b) (byte c) (byte d)).toBitVec
  rw [RSL.le32, widen a, widen b, widen c, widen d]
  exact NMX_R3_RawWord32.value a.bv b.bv c.bv d.bv
#print axioms fixed
end NMX_R3_Word32
