import AeneasWordCodec
import R1StrictWideByteCodec

set_option autoImplicit false

namespace AspisR1S5P6WordCodecBridgeV1

open Aeneas Aeneas.Std AspisV8R19.SqueezeOracleBridge
open AspisR1.RetainedFieldByteCodec

private theorem fromLEBytes_cast_toLEBytes32 {b : BitVec 32} {bs : List _root_.Byte}
    (hbs : bs = b.toLEBytes) :
    (BitVec.fromLEBytes bs).cast (by rw [hbs]; simp [BitVec.toLEBytes_length]) = b := by
  cases hbs
  have h := BitVec.fromLEBytes_toLEBytes (by decide : 32 % 8 = 0) b
  rw [h]
  simp

theorem u32_from_to_le (x : U32) :
    core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x) = x := by
  have hpoint : ∀ b : AspisV8R19.DuplexFrames.Byte, U8.bv (UScalar.mk b) = b := by
    intro b
    rfl
  have hmap : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes) = x.bv.toLEBytes := by
    rw [List.map_map]
    simpa [Function.comp_def] using congrArg (fun f : Byte → Byte => List.map f x.bv.toLEBytes)
      (funext hpoint)
  apply U32.bv_eq_imp_eq
  simp only [core.num.U32.from_le_bytes, core.num.U32.to_le_bytes]
  exact fromLEBytes_cast_toLEBytes32 hmap

def u32WordBytes (x : U32) : AspisR1.RetainedFieldByteCodec.WordBytes := fun i =>
  decodeByte ((core.num.U32.to_le_bytes x).val[i.val]'(by
    have hlen := (core.num.U32.to_le_bytes x).property
    change (core.num.U32.to_le_bytes x).val.length = 4 at hlen
    omega))

theorem u32WordBytes_decode (x : U32) :
    decodeWordLE (u32WordBytes x) = ⟨x.val, by
      change x.bv.toNat < 2^32
      exact x.bv.isLt⟩ := by
  have harray : Array.make 4#usize
      [encodeByte (u32WordBytes x 0), encodeByte (u32WordBytes x 1),
       encodeByte (u32WordBytes x 2), encodeByte (u32WordBytes x 3)] =
      core.num.U32.to_le_bytes x := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [core.num.U32.to_le_bytes]
    · intro i hi1 hi2
      have hi : i < 4 := by simpa using hi1
      interval_cases i <;> apply U8.bv_eq_imp_eq <;> apply BitVec.eq_of_toNat_eq <;> simp [u32WordBytes, core.num.U32.to_le_bytes, encodeByte, decodeByte, UScalar.ofNatCore, UScalar.val, Array.make]
  have hround : AspisR1.AeneasWordCodec.aeneasWord (u32WordBytes x) = x := by
    unfold AspisR1.AeneasWordCodec.aeneasWord
    rw [harray, u32_from_to_le]
  have hval := congrArg UScalar.val hround
  rw [AspisR1.AeneasWordCodec.aeneasWord_val_eq] at hval
  apply Fin.ext
  exact hval

theorem u32WordBytes_eq_encodeM31 (x : U32) (hx : x.val < m31Modulus) :
    u32WordBytes x = encodeM31LE ⟨x.val, hx⟩ := by
  have hdecode := u32WordBytes_decode x
  have hraw : decodeWordLE (u32WordBytes x) = m31AsRawWord ⟨x.val, hx⟩ := by
    apply Fin.ext
    exact congrArg Fin.val hdecode
  funext i
  change u32WordBytes x i = encodeWordLE (m31AsRawWord ⟨x.val, hx⟩) i
  rw [← hraw, encodeWordLE_decodeWordLE]

#print axioms u32_from_to_le
#print axioms u32WordBytes_decode
#print axioms u32WordBytes_eq_encodeM31

end AspisR1S5P6WordCodecBridgeV1
