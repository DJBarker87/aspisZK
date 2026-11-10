pat="b32, tl"
inner="⟨b32, tl⟩"
for i in range(31,-1,-1):
    inner="_ | ⟨b%d, %s⟩"%(i,inner) if i==31 else "_ | ⟨b%d, %s⟩"%(i,inner)
# build properly
s="⟨b32, tl⟩"
for i in range(31,0,-1):
    s="_ | ⟨b%d, %s⟩"%(i,s)
pattern="_ | ⟨b0, %s⟩"%s
names=" ".join("b%d"%i for i in range(32))
lst=", ".join("b%d"%i for i in range(32))
head='''import Aeneas
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

theorem lm_pack' (a b c d : Std.U8) (h : [a, b, c, d].length = 4#usize.val) :
    core.num.U32.from_le_bytes ⟨[a, b, c, d], h⟩ = pack a b c d := lm_pack a b c d

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
  rcases l with PATTERN <;> first | (exfalso; simp at width; done) | skip
  all_goals
    simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes, FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
      Slice.len, Slice.index_usize, lift, lm_pack', word32, Array.make]
'''.replace("PATTERN",pattern)
tail='''
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
  by_cases h : CanonicalWide (eWords (word32 b width))
  · simp only [h, if_true, bind_tc_ok]
    rfl
  · simp only [h, if_false, bind_tc_ok]
    rfl

#print axioms lm_pack
#print axioms native_from_limbs_shape
#print axioms from_le_bytes_shape
#print axioms e32_core
end PCVS_E32
'''
open('PRVEq_E32_s4.lean','w').write(head+tail)
