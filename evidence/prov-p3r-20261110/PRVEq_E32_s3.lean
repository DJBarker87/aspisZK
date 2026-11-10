import Aeneas
import PRVEq_Op2_p5
import PRVEq_Tx2Deployed_q6
import CheckpointBytes3EDecode
import CheckpointBytes3Word
import CheckpointBytes3EShape
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace PCVS_E32
attribute [local instance] Classical.propDecidable
open AspisR1 AspisR1.CheckpointBytes3EDecode
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
open RetainedFieldByteCodec RetainedExactLimbCodec StrictWideByteCodec WideExactLimbCodec
open AspisR1.CheckpointBytes3ScalarShape AspisR1.CheckpointBytes3EShape AspisR1.CheckpointBytes3Word AspisR1.CheckpointBytes3WordMath
open AspisR1.CheckpointBytes3KDecode MultiproofConeCanonical

theorem lm_pack (a b c d : Std.U8) :
    core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d]) = pack a b c d := by
  unfold core.num.U32.from_le_bytes pack
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Array.make, BitVec.fromLEBytes, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_cast]
  have hi' : i < 32 := by first | omega | (simp at hi; omega) | simpa using hi
  interval_cases i <;> simp

def nE (w : Fin 8 → Std.U32) : FIo_Native.aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨w 0, w 1⟩, ⟨w 2, w 3⟩⟩, ⟨⟨w 4, w 5⟩, ⟨w 6, w 7⟩⟩⟩

theorem native_from_limbs_shape (w : Fin 8 → Std.U32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]) =
      if CanonicalWide (eWords w) then ok (some (nE w)) else ok none := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs, Array.index_usize,
    FIo_Native.aspis_core.field.P]
  simp [Array.make]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]
  split <;> simp_all [CanonicalWide, Canonical, eWords, kWords, nE]

theorem from_le_bytes_shape (b : Slice Std.U8) (width : b.val.length = 32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b =
      FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
        (Array.make 8#usize [word32 b width 0, word32 b width 1, word32 b width 2, word32 b width 3,
          word32 b width 4, word32 b width 5, word32 b width 6, word32 b width 7]) := by
  obtain ⟨l, hl⟩ := b
  change l.length = 32 at width
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, ⟨b32, tl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> first | (exfalso; simp at width; done) | skip
  all_goals
    simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes, FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
      Slice.len, Slice.index_usize, lift, lm_pack, word32, Array.make]

theorem e32_core (b : Slice Std.U8) (width : b.val.length = 32) :
    NJC_ClosedCalls.inactive b = (do
      let q ← OraclePortCkptAbi2Extracted.decode_e_spec b
      ok (Option.map CheckpointBytes3Namespaces.fromE q)) := by
  have source : OraclePortCkptAbi2Extracted.decode_e_spec b =
      if CanonicalWide (eWords (word32 b width)) then
        ok (some (eWords (word32 b width))) else ok none := by
    apply e_shape b width (word32 b width)
    · simpa [word32] using word_total b 0#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 4#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 8#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 12#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 16#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 20#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 24#usize (by simp only [width]; scalar_tac)
    · simpa [word32] using word_total b 28#usize (by simp only [width]; scalar_tac)
  rw [source]
  unfold NJC_ClosedCalls.inactive NHV_InactivePacket.emitted
  rw [from_le_bytes_shape b width, native_from_limbs_shape]
  by_cases h : CanonicalWide (eWords (word32 b width)) <;> simp [h, nE, FIo_Install.fromE, CheckpointBytes3Namespaces.fromE, CheckpointBytes3Namespaces.fromK, eWords, kWords]

#print axioms lm_pack
#print axioms native_from_limbs_shape
#print axioms from_le_bytes_shape
#print axioms e32_core
end PCVS_E32
