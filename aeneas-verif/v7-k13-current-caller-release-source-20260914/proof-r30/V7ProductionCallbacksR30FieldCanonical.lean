import V7ProductionSnapshotObserverR28.FunsExternal
import V7CallerCurrentReleaseR26FieldBridge

/-!
# Arithmetic canonicality for the production query-coordinate callback

The callback is generated in a separate namespace from the verifier core.
This file connects its checked arithmetic to the already audited R26 field
model, under the representation bounds required by the source operations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ProductionSnapshotObserverR28
open V7CallerCurrentReleaseR26

namespace V7ProductionCallbacksR30FieldCanonical
theorem p_eq :
    V7ProductionCallbacksR29.aspis_core.field.P =
      V7CallerCurrentReleaseR26.field.P := by
  unfold V7ProductionCallbacksR29.aspis_core.field.P
    V7CallerCurrentReleaseR26.field.P
  apply UScalar.eq_of_val_eq
  rfl

theorem current_p_val_eq :
    V7CallerCurrentReleaseR26.field.P.val = 2147483647 := by
  unfold V7CallerCurrentReleaseR26.field.P
  rfl

theorem u32_size_eq : Std.U32.size = 4294967296 := by
  rw [Std.U32.size, Std.U32.numBits]
  norm_num

theorem uscalar_u32_size_eq : UScalar.size .U32 = 4294967296 := by
  rw [UScalar.size_UScalarTyU32, u32_size_eq]

theorem generic_wrapping_add_eq_u32_wrapping_add
    (left right : Std.U32) :
    UScalar.wrapping_add left right = Std.U32.wrapping_add left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_add_val_eq, Std.U32.wrapping_add_val_eq]

theorem generic_wrapping_sub_eq_u32_wrapping_sub
    (left right : Std.U32) :
    UScalar.wrapping_sub left right = Std.U32.wrapping_sub left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_sub_val_eq, Std.U32.wrapping_sub_val_eq]

theorem generic_wrapping_add_eq_u64_wrapping_add
    (left right : Std.U64) :
    UScalar.wrapping_add left right = Std.U64.wrapping_add left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_add_val_eq, Std.U64.wrapping_add_val_eq]

theorem generic_wrapping_mul_eq_u64_wrapping_mul
    (left right : Std.U64) :
    UScalar.wrapping_mul left right = Std.U64.wrapping_mul left right := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.wrapping_mul_val_eq, Std.U64.wrapping_mul_val_eq]

theorem checked_u64_shr31_eq_wrapping (value : Std.U64) :
    value >>> 31#u32 =
      Aeneas.Std.Result.ok (Std.U64.wrapping_shr value 31#u32) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_spec value 31#u32 (by norm_num))
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.U64.wrapping_shr value 31#u32).bv.toNat
  rw [hbv, Std.U64.wrapping_shr_bv_eq]
  norm_num

theorem checked_usize_shr_u32_eq_wrapping
    (value : Std.Usize) (shift : Std.U32)
    (hshift : shift.val < UScalarTy.Usize.numBits) :
    value >>> shift =
      Aeneas.Std.Result.ok (Std.Usize.wrapping_shr value shift) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_spec value shift hshift)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.Usize.wrapping_shr value shift).bv.toNat
  have hshiftPlatform : shift.val < System.Platform.numBits := by
    exact hshift
  rw [hbv, Std.Usize.wrapping_shr_bv_eq,
    Nat.mod_eq_of_lt hshiftPlatform]
  simp only [BitVec.ushiftRight_eq]

theorem checked_usize_shr_i32_eight_eq_wrapping (value : Std.Usize) :
    value >>> (8#i32 : Std.I32) =
      Aeneas.Std.Result.ok (Std.Usize.wrapping_shr value 8#u32) := by
  obtain ⟨output, hrun, _hval, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.ShiftRight_IScalar_spec value (8#i32 : Std.I32)
        (by norm_num) (by
          norm_num
          rcases System.Platform.numBits_eq with hbits | hbits <;>
            omega))
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (Std.Usize.wrapping_shr value 8#u32).bv.toNat
  rw [hbv, Std.Usize.wrapping_shr_bv_eq]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [hbits]

theorem u64_and_val_le_right (left right : Std.U64) :
    (left &&& right).val ≤ right.val := by
  simp only [HAnd.hAnd, instHAndUScalar, UScalar.and, UScalar.val,
    BitVec.toNat_and]
  exact Nat.and_le_right

theorem u64_wrapping_shr31_val_eq (value : Std.U64) :
    (Std.U64.wrapping_shr value 31#u32).val = value.val >>> 31 := by
  unfold Std.U64.wrapping_shr UScalar.wrapping_shr
  change (value.bv.ushiftRight (31 % 64)).toNat = value.val >>> 31
  norm_num

theorem u64_wrapping_shr31_val_le_one
    (value : Std.U64) (hvalue : value.val ≤ 4294967291) :
    (Std.U64.wrapping_shr value 31#u32).val ≤ 1 := by
  rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem u64_size_eq : Std.U64.size = 18446744073709551616 := by
  rw [Std.U64.size, Std.U64.numBits]
  norm_num

theorem checked_add_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty)
    (hbound : left.val + right.val ≤ UScalar.max ty) :
    left + right = Aeneas.Std.Result.ok (UScalar.wrapping_add left right) := by
  obtain ⟨output, hrun, _hvalue, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.add_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_add left right).bv.toNat
  rw [hbv, UScalar.wrapping_add_bv_eq]

theorem checked_sub_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty) (hbound : right.val ≤ left.val) :
    left - right = Aeneas.Std.Result.ok (UScalar.wrapping_sub left right) := by
  obtain ⟨output, hrun, _hvalue, _hbound, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.sub_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_sub left right).bv.toNat
  rw [hbv, UScalar.wrapping_sub_bv_eq]

theorem checked_usize_bits_sub_seventeen_eq_wrapping :
    core.num.Usize.BITS - 17#u32 =
      Aeneas.Std.Result.ok
        (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32) := by
  apply checked_sub_eq_wrapping
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [core.num.Usize.BITS, hbits]

theorem checked_mul_eq_wrapping {ty : UScalarTy}
    (left right : UScalar ty)
    (hbound : left.val * right.val ≤ UScalar.max ty) :
    left * right = Aeneas.Std.Result.ok (UScalar.wrapping_mul left right) := by
  obtain ⟨output, hrun, _hvalue, hbv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.mul_bv_spec (x := left) (y := right) hbound)
  rw [hrun]
  congr 2
  apply UScalar.eq_of_val_eq
  change output.bv.toNat =
    (UScalar.wrapping_mul left right).bv.toNat
  rw [hbv, UScalar.wrapping_mul_bv_eq]

theorem callback_add_eq_current_add
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V7ProductionCallbacksR29.aspis_core.field.M31.add left right =
      V7CallerCurrentReleaseR26.field.M31.add left right := by
  unfold V7ProductionCallbacksR29.aspis_core.field.M31.add
    V7CallerCurrentReleaseR26.field.M31.add
  rw [p_eq]
  rw [checked_add_eq_wrapping]
  · simp only [Std.lift, bind_tc_ok]
    by_cases hreduce :
        V7CallerCurrentReleaseR26.field.P.val ≤
          (left.val + right.val) % Std.U32.size
    · have hreduce' :
          Std.U32.wrapping_add left right ≥
            V7CallerCurrentReleaseR26.field.P := by
        apply (UScalar.le_equiv _ _).2
        simpa only [Std.U32.wrapping_add_val_eq,
          UScalar.size_UScalarTyU32] using hreduce
      simp [hreduce, hreduce']
      rw [checked_sub_eq_wrapping]
      · rw [generic_wrapping_add_eq_u32_wrapping_add,
          generic_wrapping_sub_eq_u32_wrapping_sub]
        simp
      · simpa only [UScalar.wrapping_add_val_eq,
            UScalar.size_UScalarTyU32] using hreduce
    · have hreduce' :
          ¬ Std.U32.wrapping_add left right ≥
            V7CallerCurrentReleaseR26.field.P := by
        intro h
        apply hreduce
        have hval := (UScalar.le_equiv _ _).1 h
        simpa only [Std.U32.wrapping_add_val_eq,
          UScalar.size_UScalarTyU32] using hval
      simp [hreduce, hreduce']
      exact generic_wrapping_add_eq_u32_wrapping_add left right
  · rw [UScalar.max_UScalarTy_U32_eq, Std.U32.max_eq]
    omega

theorem callback_sub_eq_current_sub
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V7ProductionCallbacksR29.aspis_core.field.M31.sub left right =
      V7CallerCurrentReleaseR26.field.M31.sub left right := by
  unfold V7ProductionCallbacksR29.aspis_core.field.M31.sub
    V7CallerCurrentReleaseR26.field.M31.sub
  rw [p_eq]
  have hadd_lt_size :
      left.val + V7CallerCurrentReleaseR26.field.P.val <
        Std.U32.size := by
    rw [current_p_val_eq, u32_size_eq]
    omega
  rw [checked_add_eq_wrapping]
  · simp only [Std.lift, bind_tc_ok]
    rw [checked_sub_eq_wrapping]
    · simp only [bind_tc_ok]
      by_cases hreduce :
          V7CallerCurrentReleaseR26.field.P.val ≤
            ((left.val + V7CallerCurrentReleaseR26.field.P.val) +
              (Std.U32.size - right.val)) % Std.U32.size
      · have hreduce' :
            (Std.U32.wrapping_add left
                V7CallerCurrentReleaseR26.field.P).wrapping_sub right ≥
              V7CallerCurrentReleaseR26.field.P := by
          apply (UScalar.le_equiv _ _).2
          simp only [Std.U32.wrapping_add_val_eq,
            Std.U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32]
          rw [Nat.mod_eq_of_lt hadd_lt_size]
          exact hreduce
        simp [hreduce, hreduce']
        rw [checked_sub_eq_wrapping]
        · rw [generic_wrapping_add_eq_u32_wrapping_add,
            generic_wrapping_sub_eq_u32_wrapping_sub,
            generic_wrapping_sub_eq_u32_wrapping_sub]
          simp
        · simp only [UScalar.wrapping_add_val_eq,
              UScalar.wrapping_sub_val_eq, UScalar.size_UScalarTyU32]
          rw [Nat.mod_eq_of_lt hadd_lt_size]
          exact hreduce
      · have hreduce' :
            ¬ (Std.U32.wrapping_add left
                V7CallerCurrentReleaseR26.field.P).wrapping_sub right ≥
              V7CallerCurrentReleaseR26.field.P := by
          intro h
          apply hreduce
          have hval := (UScalar.le_equiv _ _).1 h
          simpa only [Std.U32.wrapping_add_val_eq,
              Std.U32.wrapping_sub_val_eq, UScalar.size_UScalarTyU32,
              Nat.mod_eq_of_lt hadd_lt_size] using hval
        simp [hreduce, hreduce']
        rw [generic_wrapping_add_eq_u32_wrapping_add,
          generic_wrapping_sub_eq_u32_wrapping_sub]
    · rw [UScalar.wrapping_add_val_eq]
      rw [current_p_val_eq, uscalar_u32_size_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [UScalar.max_UScalarTy_U32_eq, Std.U32.max_eq,
      current_p_val_eq]
    omega

theorem callback_reduce_u64_eq_current_reduce_u64
    (value : Std.U64)
    (hvalue : value.val ≤ 4611686009837453316) :
    V7ProductionCallbacksR29.aspis_core.field.reduce_u64 value =
      V7CallerCurrentReleaseR26.field.reduce_u64 value := by
  unfold V7ProductionCallbacksR29.aspis_core.field.reduce_u64
    V7CallerCurrentReleaseR26.field.reduce_u64
  rw [p_eq]
  have hmask :
      (UScalar.cast .U64
        V7CallerCurrentReleaseR26.field.P).val = 2147483647 := by
    rw [Std.U32.cast_U64_val_eq, current_p_val_eq]
  have hhigh :
      (Std.U64.wrapping_shr value 31#u32).val ≤ 2147483644 := by
    rw [u64_wrapping_shr31_val_eq, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hand :
      (value &&& UScalar.cast .U64
        V7CallerCurrentReleaseR26.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  have hfirst_sum :
      (value &&& UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val ≤ 4294967291 := by
    omega
  have hfirst_sum_lt_size :
      (value &&& UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P).val +
        (Std.U64.wrapping_shr value 31#u32).val < Std.U64.size := by
    rw [u64_size_eq]
    omega
  have hx1 :
      (Std.U64.wrapping_add
        (value &&& UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P)
        (Std.U64.wrapping_shr value 31#u32)).val ≤ 4294967291 := by
    rw [Std.U64.wrapping_add_val_eq, UScalar.size_UScalarTyU64,
      Nat.mod_eq_of_lt hfirst_sum_lt_size]
    exact hfirst_sum
  have hx1high :
      (Std.U64.wrapping_shr
        (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V7CallerCurrentReleaseR26.field.P)
          (Std.U64.wrapping_shr value 31#u32)) 31#u32).val ≤ 1 := by
    exact u64_wrapping_shr31_val_le_one _ hx1
  have hx1and :
      (Std.U64.wrapping_add
          (value &&& UScalar.cast .U64
            V7CallerCurrentReleaseR26.field.P)
          (Std.U64.wrapping_shr value 31#u32) &&&
        UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P).val ≤ 2147483647 := by
    calc
      _ ≤ (UScalar.cast .U64
          V7CallerCurrentReleaseR26.field.P).val :=
        u64_and_val_le_right _ _
      _ = 2147483647 := hmask
  simp only [Std.lift, bind_tc_ok]
  rw [checked_u64_shr31_eq_wrapping]
  simp only [bind_tc_ok]
  rw [checked_add_eq_wrapping]
  · simp only [bind_tc_ok]
    rw [generic_wrapping_add_eq_u64_wrapping_add]
    rw [checked_u64_shr31_eq_wrapping]
    simp only [bind_tc_ok]
    rw [checked_add_eq_wrapping]
    · simp only [bind_tc_ok]
      rw [generic_wrapping_add_eq_u64_wrapping_add]
      by_cases hreduce :
          UScalar.cast .U32
              (Std.U64.wrapping_add
                (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V7CallerCurrentReleaseR26.field.P)
                    (Std.U64.wrapping_shr value 31#u32) &&&
                  UScalar.cast .U64
                    V7CallerCurrentReleaseR26.field.P)
                (Std.U64.wrapping_shr
                  (Std.U64.wrapping_add
                    (value &&& UScalar.cast .U64
                      V7CallerCurrentReleaseR26.field.P)
                    (Std.U64.wrapping_shr value 31#u32)) 31#u32)) ≥
            V7CallerCurrentReleaseR26.field.P
      · simp [hreduce]
        rw [checked_sub_eq_wrapping]
        · rw [generic_wrapping_sub_eq_u32_wrapping_sub]
        · exact (UScalar.le_equiv _ _).1 hreduce
      · simp [hreduce]
    · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
      omega
  · rw [UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega

theorem callback_mul_eq_current_mul
    (left right : Std.U32)
    (hleft : left.val < 2147483647)
    (hright : right.val < 2147483647) :
    V7ProductionCallbacksR29.aspis_core.field.M31.mul left right =
      V7CallerCurrentReleaseR26.field.M31.mul left right := by
  have hproduct : left.val * right.val ≤ 4611686009837453316 := by
    nlinarith
  have hwrapped :
      (Std.U64.wrapping_mul (UScalar.cast .U64 left)
        (UScalar.cast .U64 right)).val = left.val * right.val := by
    rw [Std.U64.wrapping_mul_val_eq, UScalar.size_UScalarTyU64,
      Std.U32.cast_U64_val_eq, Std.U32.cast_U64_val_eq]
    rw [Nat.mod_eq_of_lt]
    rw [u64_size_eq]
    omega
  unfold V7ProductionCallbacksR29.aspis_core.field.M31.mul
    V7CallerCurrentReleaseR26.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [checked_mul_eq_wrapping]
  · simp only [bind_tc_ok]
    rw [generic_wrapping_mul_eq_u64_wrapping_mul]
    rw [callback_reduce_u64_eq_current_reduce_u64]
    rw [hwrapped]
    exact hproduct
  · rw [Std.U32.cast_U64_val_eq, Std.U32.cast_U64_val_eq,
      UScalar.max_UScalarTy_U64_eq, Std.U64.max_eq]
    omega
open V7CallerCurrentReleaseR26FieldBridge

abbrev CallbackM31 := V7ProductionCallbacksR29.aspis_core.field.M31

theorem callback_m31_mul_canonical
    (left right : CallbackM31)
    (hleft : AspisAeneasCM31Multiplicative.CanonicalRawM31 left.val)
    (hright : AspisAeneasCM31Multiplicative.CanonicalRawM31 right.val) :
    ∃ output : CallbackM31,
      V7ProductionCallbacksR29.aspis_core.field.M31.mul left right = ok output ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨output, currentRun, canonical, _⟩ :=
    generated_m31_mul_corresponds left right hleft hright
  refine ⟨output, ?_, canonical⟩
  rw [callback_mul_eq_current_mul left right]
  · exact currentRun
  · exact hleft
  · exact hright

theorem callback_m31_double_canonical
    (value : CallbackM31)
    (canonical : AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val) :
    ∃ output : CallbackM31,
      V7ProductionCallbacksR29.aspis_core.field.M31.double value = ok output ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨output, currentRun, outputCanonical, _⟩ :=
    generated_m31_add_corresponds value value canonical canonical
  refine ⟨output, ?_, outputCanonical⟩
  unfold V7ProductionCallbacksR29.aspis_core.field.M31.double
  rw [callback_add_eq_current_add value value]
  · exact currentRun
  · exact canonical
  · exact canonical

theorem callback_m31_sub_canonical
    (left right : CallbackM31)
    (hleft : AspisAeneasCM31Multiplicative.CanonicalRawM31 left.val)
    (hright : AspisAeneasCM31Multiplicative.CanonicalRawM31 right.val) :
    ∃ output : CallbackM31,
      V7ProductionCallbacksR29.aspis_core.field.M31.sub left right = ok output ∧
      AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val := by
  obtain ⟨output, currentRun, canonical, _⟩ :=
    generated_m31_sub_corresponds left right hleft hright
  refine ⟨output, ?_, canonical⟩
  rw [callback_sub_eq_current_sub left right]
  · exact currentRun
  · exact hleft
  · exact hright

#print axioms callback_m31_mul_canonical
#print axioms callback_m31_double_canonical
#print axioms callback_m31_sub_canonical

end V7ProductionCallbacksR30FieldCanonical
