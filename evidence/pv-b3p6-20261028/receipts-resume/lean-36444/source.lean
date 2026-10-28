import PV_B3P_EndianLane226V3
import PV_B3P_ByteLayout226V3
namespace PV_B3P_EndianVerified226V3
open Aeneas Aeneas.Std PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem lane_nat {w : Nat} (v : BitVec w) (i : Nat) (h : 8*i+8 ≤ w)
    (hi : i < v.toLEBytes.length) :
    (v.toLEBytes[i]).toNat = (v.toNat >>> (8*i)) % 256 := by
  have hh := congrArg BitVec.toNat (PV_B3P_EndianLane226V3.lane v i h hi)
  simpa only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight] using hh

theorem word_bytes (v : U32) : wordBytes v = (core.num.U32.to_le_bytes v).val := by
  apply List.ext_getElem
  · change (wordBytes v).length = (List.map (@UScalar.mk .U8) v.bv.toLEBytes).length
    rw [List.length_map,BitVec.toLEBytes_length]
    rfl
  · intro i hi hj
    have hn : i < 4 := by simpa only [wordBytes,List.length_cons,List.length_nil] using hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simp only [wordBytes,core.num.U32.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 v).val = (v.bv.toLEBytes[0]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change v.bv.toNat % 256 = _
      simpa only [Nat.mul_zero,Nat.shiftRight_zero] using
        (lane_nat v.bv 0 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [wordBytes,core.num.U32.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U32.wrapping_shr v 8#u32)).val = (v.bv.toLEBytes[1]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U32.wrapping_shr v 8#u32).bv.toNat % 256 = _
      rw [U32.wrapping_shr_bv_eq]
      change (v.bv >>> 8).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 1 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [wordBytes,core.num.U32.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U32.wrapping_shr v 16#u32)).val = (v.bv.toLEBytes[2]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U32.wrapping_shr v 16#u32).bv.toNat % 256 = _
      rw [U32.wrapping_shr_bv_eq]
      change (v.bv >>> 16).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 2 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [wordBytes,core.num.U32.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U32.wrapping_shr v 24#u32)).val = (v.bv.toLEBytes[3]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U32.wrapping_shr v 24#u32).bv.toNat % 256 = _
      rw [U32.wrapping_shr_bv_eq]
      change (v.bv >>> 24).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 3 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm

#print axioms word_bytes

theorem index_bytes (v : U64) : indexBytes v = (core.num.U64.to_le_bytes v).val := by
  apply List.ext_getElem
  · change (indexBytes v).length = (List.map (@UScalar.mk .U8) v.bv.toLEBytes).length
    rw [List.length_map,BitVec.toLEBytes_length]
    rfl
  · intro i hi hj
    have hn : i < 8 := by simpa only [indexBytes,List.length_cons,List.length_nil] using hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 v).val = (v.bv.toLEBytes[0]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change v.bv.toNat % 256 = _
      simpa only [Nat.mul_zero,Nat.shiftRight_zero] using
        (lane_nat v.bv 0 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 8#u32)).val = (v.bv.toLEBytes[1]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 8#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 8).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 1 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 16#u32)).val = (v.bv.toLEBytes[2]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 16#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 16).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 2 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 24#u32)).val = (v.bv.toLEBytes[3]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 24#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 24).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 3 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 32#u32)).val = (v.bv.toLEBytes[4]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 32#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 32).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 4 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 40#u32)).val = (v.bv.toLEBytes[5]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 40#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 40).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 5 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 48#u32)).val = (v.bv.toLEBytes[6]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 48#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 48).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 6 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm
    · simp only [indexBytes,core.num.U64.to_le_bytes,List.getElem_map,
        List.getElem_cons_zero,List.getElem_cons_succ]
      apply UScalar.eq_of_val_eq
      change (UScalar.cast .U8 (U64.wrapping_shr v 56#u32)).val = (v.bv.toLEBytes[7]'(by rw [BitVec.toLEBytes_length]; decide)).toNat
      rw [UScalar.cast_val_eq]
      change (U64.wrapping_shr v 56#u32).bv.toNat % 256 = _
      rw [U64.wrapping_shr_bv_eq]
      change (v.bv >>> 56).toNat % 256 = _
      rw [BitVec.toNat_ushiftRight]
      exact (lane_nat v.bv 7 (by decide) (by rw [BitVec.toLEBytes_length]; decide)).symm

#print axioms index_bytes

#print axioms lane_nat
end PV_B3P_EndianVerified226V3
