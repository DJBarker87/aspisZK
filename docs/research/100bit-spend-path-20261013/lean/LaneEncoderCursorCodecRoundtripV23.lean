import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailCursorCodec
open Aeneas Aeneas.Std

theorem fromLEBytes_cast_toLEBytes {b : BitVec 64} {bs : List Byte}
    (hbs : bs = b.toLEBytes) :
    (BitVec.fromLEBytes bs).cast (by rw [hbs]; simp [BitVec.toLEBytes_length]) = b := by
  cases hbs
  have h := BitVec.fromLEBytes_toLEBytes (by decide : 64 % 8 = 0) b
  rw [h]
  simp

theorem u64_from_to_le (x : U64) :
    core.num.U64.from_le_bytes (core.num.U64.to_le_bytes x) = x := by
  have hpoint : ∀ b : Byte, U8.bv (UScalar.mk b) = b := by
    intro b
    rfl
  have hmap : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes) = x.bv.toLEBytes := by
    rw [List.map_map]
    simpa [Function.comp_def] using congrArg (fun f : Byte → Byte => List.map f x.bv.toLEBytes)
      (funext hpoint)
  apply U64.bv_eq_imp_eq
  simp only [core.num.U64.from_le_bytes, core.num.U64.to_le_bytes]
  exact fromLEBytes_cast_toLEBytes hmap

#print axioms u64_from_to_le
end AspisR1PairForestLaneEncoderTailCursorCodec
