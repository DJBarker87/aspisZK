import CheckpointBytes3KDecode
import CheckpointBytes3EShape

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes3EDecode
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
open RetainedFieldByteCodec RetainedExactLimbCodec StrictWideByteCodec WideExactLimbCodec
open CheckpointBytes3ScalarShape CheckpointBytes3EShape CheckpointBytes3Word CheckpointBytes3WordMath
open CheckpointBytes3KDecode MultiproofConeCanonical
attribute [local instance] Classical.propDecidable

def rawE (x : OraclePortCheckpointAbiC5.E) : aspis_core.field.wide_exact.WideExact :=
  ⟨rawK x.re,rawK x.im⟩

def fixed32 (b : Slice U8) (width : b.val.length = 32) : WideBytes :=
  fun j => AspisV8R19.SqueezeOracleBridge.decodeByte (b.val[j.val]'(by omega))

def word32 (b : Slice U8) (width : b.val.length = 32) (j : Fin 8) : U32 :=
  pack (b.val[4*j.val]'(by omega)) (b.val[4*j.val+1]'(by omega))
    (b.val[4*j.val+2]'(by omega)) (b.val[4*j.val+3]'(by omega))

theorem low_word_model (b : Slice U8) (width : b.val.length = 32) (j : Fin 4) :
    (word32 b width ⟨j.val,by omega⟩).val =
      (decodeWordLE (qm31LimbBytes (lowBytes (fixed32 b width)) j)).val := by
  rw [word32,pack_value]
  fin_cases j <;> rfl

theorem high_word_model (b : Slice U8) (width : b.val.length = 32) (j : Fin 4) :
    (word32 b width ⟨j.val+4,by omega⟩).val =
      (decodeWordLE (qm31LimbBytes (highBytes (fixed32 b width)) j)).val := by
  rw [word32,pack_value]
  fin_cases j <;> rfl

theorem raw_pair (lo hi : QM31Limbs) :
    rawE (pairExactEquiv (lo,hi)) =
      (⟨rawLimbs lo,rawLimbs hi⟩ : aspis_core.field.wide_exact.WideExact) := by
  change (⟨rawK (qm31ExactLimbEquiv lo),rawK (qm31ExactLimbEquiv hi)⟩ :
    aspis_core.field.wide_exact.WideExact) = _
  simp only [rawK,Equiv.symm_apply_apply]

theorem fixed_decode (b : Slice U8) (width : b.val.length = 32) :
    (FoldedLeafCodec.decodeWide (bytesOf b.val)).map rawE =
      (do let lo ← (decodeQM31LE (lowBytes (fixed32 b width))).map rawLimbs
          let hi ← (decodeQM31LE (highBytes (fixed32 b width))).map rawLimbs
          some (⟨lo,hi⟩ : aspis_core.field.wide_exact.WideExact)) := by
  have fb : fixedBytes? 32 (bytesOf b.val) = some (fixed32 b width) := by
    unfold fixedBytes?
    rw [dif_pos (by simpa [bytesOf] using width)]
    congr 1
    funext j
    simp [bytesOf,fixed32]
  simp only [FoldedLeafCodec.decodeWide,fb,Option.bind_some,decodeWideLE]
  cases hlo : decodeQM31LE (lowBytes (fixed32 b width)) <;>
    cases hhi : decodeQM31LE (highBytes (fixed32 b width)) <;>
    simp [hlo,hhi,raw_pair]

/-- The strict eight-limb Result, including every canonicality rejection. -/
theorem decode_e_identification (b : Slice U8) (width : b.val.length = 32) :
    decode_e_spec b = ok ((FoldedLeafCodec.decodeWide (bytesOf b.val)).map rawE) := by
  rw [fixed_decode b width]
  rw [model_shape _ (fun j => word32 b width ⟨j.val,by omega⟩) (low_word_model b width),
    model_shape _ (fun j => word32 b width ⟨j.val+4,by omega⟩) (high_word_model b width)]
  have source : decode_e_spec b =
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
  by_cases lo : Canonical (eWords (word32 b width)).c0 <;>
    by_cases hi : Canonical (eWords (word32 b width)).c1 <;>
    simp_all [CanonicalWide,eWords]

theorem reject_e (b : Slice U8) (width : b.val.length = 32) :
    decode_e_spec b = ok none ↔ FoldedLeafCodec.decodeWide (bytesOf b.val) = none := by
  rw [decode_e_identification b width]
  simp

theorem successful_e (b : Slice U8) (width : b.val.length = 32)
    (q : aspis_core.field.wide_exact.WideExact) :
    decode_e_spec b = ok (some q) ↔
      ∃ x, FoldedLeafCodec.decodeWide (bytesOf b.val) = some x ∧ rawE x = q := by
  rw [decode_e_identification b width]
  simp

#print axioms low_word_model
#print axioms high_word_model
#print axioms raw_pair
#print axioms fixed_decode
#print axioms decode_e_identification
#print axioms reject_e
#print axioms successful_e
end AspisR1.CheckpointBytes3EDecode
end
