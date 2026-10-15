import R1PublicIndexCodec
import AeneasWordCodec

/-! Bridge the existing Aeneas `U64.from_le_bytes` primitive to the retained
mathematical eight-byte public-index codec. This is an unconditional
representation lemma for every fixed-size Aeneas byte array; it does not make
a Rust source or caller-width correspondence claim. -/
set_option autoImplicit false

namespace AspisR1.PublicIndexAeneas

open Aeneas Aeneas.Std
open AspisR1.RetainedFieldByteCodec
open AspisV8R19.SqueezeOracleBridge

def arrayBytes8 (a : Array U8 8#usize) : PublicIndexCodec.IndexBytes :=
  fun i => decodeByte (a.val[i.val]'(by
    have hlen : a.val.length = 8 := a.property
    omega))

private theorem fromLEBytes_eight (b0 b1 b2 b3 b4 b5 b6 b7 : U8) :
    (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv,
      b4.bv, b5.bv, b6.bv, b7.bv]).toNat =
      b0.val + 256 * b1.val + 65536 * b2.val +
        16777216 * b3.val + 4294967296 * b4.val +
        1099511627776 * b5.val + 281474976710656 * b6.val +
        72057594037927936 * b7.val := by
  rw [AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons,
    AspisV8R19.SamplerWordBridge.byte_cons]
  simp only [UScalar.val]
  omega

/-- The Aeneas U64 little-endian primitive returns the same natural value as
the two-word public-index codec, for every eight-byte input. -/
theorem u64_from_le_bytes_matches (a : Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).val =
      (PublicIndexCodec.decode (arrayBytes8 a)).val := by
  change (BitVec.fromLEBytes (a.val.map U8.bv)).toNat =
    (decodeWordLE (fun i => arrayBytes8 a ⟨i.val, by omega⟩)).val +
      2 ^ 32 * (decodeWordLE (fun i => arrayBytes8 a ⟨i.val + 4, by omega⟩)).val
  let b0 := a.val[0]'(by have h := a.property; omega)
  let b1 := a.val[1]'(by have h := a.property; omega)
  let b2 := a.val[2]'(by have h := a.property; omega)
  let b3 := a.val[3]'(by have h := a.property; omega)
  let b4 := a.val[4]'(by have h := a.property; omega)
  let b5 := a.val[5]'(by have h := a.property; omega)
  let b6 := a.val[6]'(by have h := a.property; omega)
  let b7 := a.val[7]'(by have h := a.property; omega)
  have hlist : a.val.map U8.bv =
      [b0.bv, b1.bv, b2.bv, b3.bv, b4.bv, b5.bv, b6.bv, b7.bv] := by
    apply List.ext_getElem
    · simp [a.property]
    · intro i hi hj
      have hi8 : i < 8 := by simpa using hj
      interval_cases i <;> simp [b0, b1, b2, b3, b4, b5, b6, b7]
  rw [hlist, fromLEBytes_eight]
  simp [arrayBytes8, decodeByte, decodeWordLE,
    b0, b1, b2, b3, b4, b5, b6, b7]
  omega

#print axioms u64_from_le_bytes_matches

end AspisR1.PublicIndexAeneas
