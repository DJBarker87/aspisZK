import AspisR1S3InactiveSource.Funs

set_option autoImplicit false
namespace AspisR1.S3InactiveExecutionBridge

open Aeneas Aeneas.Std Result WP

abbrev Usize := UScalar UScalarTy.Usize
abbrev U16 := UScalar UScalarTy.U16

def inactiveMaskBit (mask : U16) (r : Usize) : Bool :=
  decide (((mask.val >>> (r.val % 16)) &&& 1) = 0)

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The extracted helper returns the bit selected by the actual pinned mask
array whenever its guarded row is in range. -/
theorem inactive_mask_exec_spec (r : Usize)
    (hbelow : ¬ r ≥ 1024#usize) (hr : r.val < 1024) :
    ∃ i mask,
      i.val = r.val / 16 ∧
      Array.index_usize AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS i = .ok mask ∧
      AspisR1S3InactiveSource.r0.opening.inactive r =
        .ok (core.result.Result.Ok (inactiveMaskBit mask r)) := by
  have h16 : (16#usize).val = 16 := by norm_num [UScalar.ofNatCore_val_eq]
  have hden : (16#usize).val ≠ 0 := by rw [h16]; omega
  obtain ⟨i, hdiv, hdivVal⟩ := @UScalar.div_spec .Usize r (16#usize) hden
  have hdivVal : i.val = r.val / 16 := by simpa [h16] using hdivVal
  have hi : i.val < 64 := by rw [hdivVal]; omega
  have hArrayBound : i.val < AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.length := by
    change i.val < (64#usize).val
    simpa [UScalar.ofNatCore_val_eq] using hi
  obtain ⟨mask, hread, hreadVal⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec
      AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS i hArrayBound)
  have hremSpec := UScalar.rem_spec r (y := 16#usize) hden
  obtain ⟨rem, hremRun, hremVal⟩ := WP.spec_imp_exists hremSpec
  have hrem : UScalar.rem r (16#usize) = .ok rem := by
    simpa [HMod.hMod] using hremRun
  have hremVal : rem.val = r.val % 16 := by simpa [h16] using hremVal
  have hremBound : rem.val < UScalarTy.U16.numBits := by
    rw [hremVal]
    have hwidth : UScalarTy.U16.numBits = 16 := by decide
    rw [hwidth]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨shifted, hshift, hshiftSpec⟩ :=
    WP.spec_imp_exists (UScalar.ShiftRight_spec mask rem hremBound)
  obtain ⟨bit, hand, handSpec⟩ :=
    WP.spec_imp_exists (UScalar.and_spec shifted (1#u16))
  have hone : (1#u16).val = 1 := by norm_num [UScalar.ofNatCore_val_eq]
  have hzero : (0#u16).val = 0 := by simp [UScalar.ofNatCore_val_eq]
  have hbitVal : bit.val = ((mask.val >>> rem.val) &&& 1) := by
    calc
      bit.val = bit.bv.toNat := rfl
      _ = (shifted.bv &&& (1#u16).bv).toNat := by rw [handSpec.2]
      _ = (mask.bv >>> rem.val &&& (1#u16).bv).toNat := by rw [hshiftSpec.2]
      _ = ((mask.val >>> rem.val) &&& 1) := by
        rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
        simp [UScalar.bv_toNat]
  have hbitIff : bit = 0#u16 ↔ ((mask.val >>> rem.val) &&& 1) = 0 := by
    constructor
    · intro heq
      have hv := congrArg UScalar.val heq
      rw [hzero, hbitVal] at hv
      exact hv
    · intro hv
      apply UScalar.eq_of_val_eq
      rw [hbitVal, hzero]
      exact hv
  have hbitDecide : decide (bit = 0#u16) = decide (((mask.val >>> rem.val) &&& 1) = 0) :=
    congrArg (fun p : Prop => decide p) (propext hbitIff)
  refine ⟨i, mask, hdivVal, hread, ?_⟩
  unfold AspisR1S3InactiveSource.r0.opening.inactive
  simp only [if_neg hbelow, hdiv, hread, HMod.hMod, hrem, hshift, hand, lift, bind_tc_ok]
  simp [inactiveMaskBit, hbitDecide, hremVal]

#print axioms inactive_mask_exec_spec
end AspisR1.S3InactiveExecutionBridge
