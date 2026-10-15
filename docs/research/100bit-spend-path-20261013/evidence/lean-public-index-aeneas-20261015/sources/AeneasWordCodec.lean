import AspisV8R19.SamplerWordBridge
import R1RetainedFieldByteCodec

/-! Connect the existing extracted four-byte U32 decoder theorem to the
retained mathematical little-endian word codec for arbitrary four-byte input.
This is a representation lemma, not a current Rust source correspondence. -/
set_option autoImplicit false

namespace AspisR1.AeneasWordCodec

open Aeneas Aeneas.Std AspisV8R19.SqueezeOracleBridge
open AspisR1.RetainedFieldByteCodec

def aeneasWord (bytes : WordBytes) : U32 :=
  core.num.U32.from_le_bytes
    (Array.make 4#usize
      [encodeByte (bytes 0), encodeByte (bytes 1),
       encodeByte (bytes 2), encodeByte (bytes 3)])

theorem aeneasWord_val_eq (bytes : WordBytes) :
    (aeneasWord bytes).val = (decodeWordLE bytes).val := by
  rw [aeneasWord, AspisV8R19.SamplerWordBridge.four_bytes]
  simp [encodeByte, decodeWordLE]

#print axioms aeneasWord_val_eq

end AspisR1.AeneasWordCodec
