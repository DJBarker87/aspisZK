import Aeneas
import R1RetainedFieldByteCodec
/-! Exact word-byte bridge via a pure BitVec lemma. No scalar-byte simp
procedure participates in the bit-level arithmetic proof. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWordBytes47
open Aeneas Aeneas.Std AspisR1.RetainedFieldByteCodec

def rawByte (x : U8) : AspisR1.RetainedFieldByteCodec.Byte := x.bv.toFin
def rawWord (x : U32) : RawWord := x.bv.toFin

def bits (w : BitVec 32) : WordBytes := fun i =>
  (w.toLEBytes[i.val]'(by simpa only [BitVec.toLEBytes_length] using i.isLt)).toFin

theorem bits_decode (w : BitVec 32) : decodeWordLE (bits w)=w.toFin := by
  apply Fin.ext
  have hw := w.isLt
  simp [decodeWordLE,bits,BitVec.toLEBytes,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  omega

theorem bits_word (w : BitVec 32) : w.toLEBytes.map BitVec.toFin=
    List.ofFn (encodeWordLE w.toFin) := by
  have hc : encodeWordLE w.toFin=bits w := by
    rw [← bits_decode w]
    exact encodeWordLE_decodeWordLE _
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_map,BitVec.toLEBytes_length,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,bits]

theorem word (x : U32) : (core.num.U32.to_le_bytes x).val.map rawByte=
    List.ofFn (encodeWordLE (rawWord x)) := by
  change (x.bv.toLEBytes.map (@UScalar.mk .U8)).map rawByte = _
  rw [List.map_map]
  exact bits_word x.bv

#print axioms bits_decode
#print axioms bits_word
#print axioms word
end R1Z.ProverCommitWordBytes47
