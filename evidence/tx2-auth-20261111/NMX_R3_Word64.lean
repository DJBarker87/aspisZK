import NMX_R3_LongBits
import NMX_R3_RawWord64
import NMX_R3_PrimaryWindow
set_option autoImplicit false
namespace NMX_R3_Word64
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

def array (v : Fin 8 → U8) : Array U8 8#usize :=
 Array.make 8#usize [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]

theorem fixed (v : Fin 8 → U8) :
 long (core.num.U64.from_le_bytes (array v)) =
 RSL.le64 [byte (v 0), byte (v 1), byte (v 2), byte (v 3),
  byte (v 4), byte (v 5), byte (v 6), byte (v 7)] := by
 apply UInt64.toBitVec_inj.mp
 rw [NMX_R3_LongBits.value]
 change NMX_R3_RawWord64Defs.encoded (fun i => (v i).bv) =
  (RSL.le64 [byte (v 0), byte (v 1), byte (v 2), byte (v 3),
   byte (v 4), byte (v 5), byte (v 6), byte (v 7)]).toBitVec
 unfold RSL.le64
 change NMX_R3_RawWord64Defs.encoded (fun i => (v i).bv) =
  ([byte (v 0), byte (v 1), byte (v 2), byte (v 3),
   byte (v 4), byte (v 5), byte (v 6), byte (v 7)].foldr
    (fun (x : UInt8) (acc : UInt64) => (acc <<< 8) ||| x.toUInt64) 0).toBitVec
 simp only [List.foldr, NMX_R3_LongBits.byte_widen]
 exact NMX_R3_RawWord64.value (fun i => (v i).bv)

/-- Total word read and canonical fold at exactly the original byte window. -/
theorem value (b : Slice U8) (s : Usize) (fit : s.val+8 ≤ b.val.length) :
 ∃ w : U64, NCV_Reference.word64 b s = ok w ∧
  long w = RSL.le64 (RSL.slice (b.val.map byte) s.val (s.val+8)) := by
 let v : Fin 8 → U8 := fun i => NCV_ZeroStep.byte b (s.val+i.val)
 have window : NDB_PrimaryWords.window b s.val 8#usize = array v := by
  apply Subtype.ext
  rfl
 have contents : (b.val.drop s.val).take 8 = (array v).val :=
  (NMX_R3_PrimaryWindow.bytes b s.val 8#usize fit).symm.trans (congrArg Subtype.val window)
 have image : RSL.slice (b.val.map byte) s.val (s.val+8) = (array v).val.map byte := by
  rw [NMX_R3_ByteCarrier.window, show s.val+8-s.val=8 by omega, contents]
 refine ⟨core.num.U64.from_le_bytes (array v), ?_, ?_⟩
 · rw [NDB_PrimaryWords.word64 b s fit, window]
 · rw [image]
   exact fixed v
#print axioms fixed
#print axioms value
end NMX_R3_Word64
