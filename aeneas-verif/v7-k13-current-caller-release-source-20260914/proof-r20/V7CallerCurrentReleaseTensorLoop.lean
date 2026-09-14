import V7CallerCurrentReleaseFieldBridge

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators

namespace V7CallerCurrentReleaseTensorLoop

open V7CallerCurrentReleaseFieldBridge

abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31
instance : Inhabited QM31 := ⟨V7CallerCurrentReleaseR20.field.QM31.ZERO⟩

def CanonicalSlice (values : Slice QM31) : Prop :=
  ∀ i, i < values.length → GeneratedCanonicalQM31 values.val[i]!

def usizeOfNatTruncate (value : Nat) : Std.Usize :=
  UScalar.ofNatCore (value % (2 ^ UScalarTy.Usize.numBits)) (by
    exact Nat.mod_lt _ (by positivity))

private theorem usizeOfNatTruncate_val_eq {value : Nat}
    (h : value < UScalar.size .Usize) :
    (usizeOfNatTruncate value).val = value := by
  simp only [usizeOfNatTruncate, UScalar.ofNatCore_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [UScalar.size_def] using h

def selectedBit (width : Nat) (index : Std.U32) (coordinate : Nat) : Std.U32 :=
  (Std.U32.wrapping_shr index
      (UScalar.cast .U32
        (usizeOfNatTruncate (width - 1 - coordinate)))) &&&
    1#u32

def tensorFactor (factors : Slice QM31) (index : Std.U32)
    (coordinate : Nat) : ExactQM31 :=
  if selectedBit factors.length index coordinate != 0#u32 then
    generatedQm31ToExact factors.val[coordinate]!
  else 1

def tensorPrefix (scale : QM31) (factors : Slice QM31)
    (index : Std.U32) (processed : Nat) : ExactQM31 :=
  generatedQm31ToExact scale *
    ∏ coordinate ∈ Finset.range processed, tensorFactor factors index coordinate

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (hIndex : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using hIndex))
  have hList : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using hIndex
  simpa [hValue, hList] using hRun

private theorem usize_succ_run (coordinate : Std.Usize)
    (h : coordinate.val < UScalar.size .Usize - 1) :
    Std.Usize.wrapping_add coordinate 1#usize =
      usizeOfNatTruncate (coordinate.val + 1) := by
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_add_val_eq]
  rw [usizeOfNatTruncate_val_eq]
  · apply Nat.mod_eq_of_lt
    have hsize : 0 < UScalar.size .Usize := by simp [UScalar.size_def]
    have hone : (1#usize).val = 1 := by norm_num
    omega
  · omega

private theorem usize_wrapping_sub_eq (left right : Std.Usize)
    (hLe : right.val ≤ left.val) :
    Std.Usize.wrapping_sub left right =
      usizeOfNatTruncate (left.val - right.val) := by
  have hSize : 0 < UScalar.size .Usize := by simp [UScalar.size_def]
  have hLeft : left.val < UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact left.bv.isLt
  have hDiff : left.val - right.val < UScalar.size .Usize := by omega
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_sub_val_eq,
    usizeOfNatTruncate_val_eq hDiff]
  have hRearrange :
      left.val + (UScalar.size .Usize - right.val) =
        (left.val - right.val) + UScalar.size .Usize := by omega
  rw [hRearrange, Nat.add_mod_right, Nat.mod_eq_of_lt hDiff]

def TensorInvariant (scale current : QM31) (factors : Slice QM31)
    (index : Std.U32) (coordinate : Nat) : Prop :=
  GeneratedCanonicalQM31 current ∧
    generatedQm31ToExact current = tensorPrefix scale factors index coordinate

private theorem tensor_body_done
    (factors : Slice QM31) (index : Std.U32) (current : QM31)
    (coordinate : Std.Usize) (hDone : ¬ coordinate.val < factors.length) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop.body
      factors index current coordinate = ok (done current) := by
  unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop.body
  simp [hDone]

private theorem tensor_body_active
    (scale current : QM31) (factors : Slice QM31) (index : Std.U32)
    (coordinate : Std.Usize)
    (hWidth : factors.length ≤ 32)
    (hCanonical : CanonicalSlice factors)
    (hActive : coordinate.val < factors.length)
    (hInvariant : TensorInvariant scale current factors index coordinate.val) :
    ∃ next out,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop.body
          factors index current coordinate = ok (cont (out, next)) ∧
      next.val = coordinate.val + 1 ∧
      TensorInvariant scale out factors index next.val := by
  let raw := factors.val[coordinate.val]!
  have hread : Slice.index_usize factors coordinate = ok raw :=
    slice_index_run factors coordinate hActive
  have hrawCanonical : GeneratedCanonicalQM31 raw :=
    hCanonical coordinate.val hActive
  let bit := selectedBit factors.length index coordinate.val
  have hshiftBound : factors.length - 1 - coordinate.val < 32 := by omega
  have hUsizeLarge : 32 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  have hshiftUsizeVal :
      (usizeOfNatTruncate (factors.length - 1 - coordinate.val)).val =
        factors.length - 1 - coordinate.val :=
    usizeOfNatTruncate_val_eq (by omega)
  have hshiftCast :
      (UScalar.cast .U32
        (usizeOfNatTruncate (factors.length - 1 - coordinate.val))).val =
        factors.length - 1 - coordinate.val := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · exact hshiftUsizeVal
    · rw [hshiftUsizeVal]
      exact lt_trans hshiftBound (by norm_num)
  have hlenVal : (Slice.len factors).val = factors.length := by simp
  have hminusOne :
      Std.Usize.wrapping_sub (Slice.len factors) 1#usize =
        usizeOfNatTruncate (factors.length - 1) := by
    have h := usize_wrapping_sub_eq (Slice.len factors) 1#usize (by
      have hPositive : 1 ≤ factors.length := by omega
      simpa [hlenVal] using hPositive)
    simpa [hlenVal] using h
  have hminusOneVal :
      (usizeOfNatTruncate (factors.length - 1)).val = factors.length - 1 :=
    usizeOfNatTruncate_val_eq (by omega)
  have hminusCoordinate :
      Std.Usize.wrapping_sub (usizeOfNatTruncate (factors.length - 1)) coordinate =
        usizeOfNatTruncate (factors.length - 1 - coordinate.val) := by
    have h := usize_wrapping_sub_eq
      (usizeOfNatTruncate (factors.length - 1)) coordinate (by
        rw [hminusOneVal]
        omega)
    simpa [hminusOneVal] using h
  have hnextRoom : coordinate.val < UScalar.size .Usize - 1 := by
    omega
  let next := usizeOfNatTruncate (coordinate.val + 1)
  have hnext := usize_succ_run coordinate hnextRoom
  have hnextVal : next.val = coordinate.val + 1 := by
    apply usizeOfNatTruncate_val_eq
    omega
  have hActiveScalar : coordinate < Slice.len factors := by
    simpa [hlenVal] using hActive
  by_cases hbit : bit != 0#u32
  · obtain ⟨out, hout, houtCanonical, houtExact⟩ :=
      generated_qm31_mul_corresponds current raw hInvariant.1 hrawCanonical
    refine ⟨next, out, ?_, hnextVal, ?_⟩
    · unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop.body
      rw [if_pos hActiveScalar]
      simp only [bind_tc_ok, Std.lift]
      rw [hminusOne, hminusCoordinate]
      change
        (if bit != 0#u32 then
            (Slice.index_usize factors coordinate >>= fun q =>
              V7CallerCurrentReleaseR20.field.QM31.mul current q >>= fun value1 =>
                ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize)))
          else ok (cont (current, Std.Usize.wrapping_add coordinate 1#usize))) = _
      rw [if_pos hbit, hread]
      simp only [bind_tc_ok]
      rw [hout]
      simp only [bind_tc_ok]
      rw [hnext]
    · refine ⟨houtCanonical, ?_⟩
      rw [houtExact, hInvariant.2]
      have hbitNe : bit ≠ 0#u32 := by simpa using hbit
      have hbitVal : bit.val ≠ 0 := by
        intro hzero
        apply hbitNe
        apply UScalar.eq_of_val_eq
        simpa using hzero
      simp [tensorPrefix, Finset.prod_range_succ, tensorFactor, hnextVal,
        bit, hbitVal, raw, hActive]
      ring
  · refine ⟨next, current, ?_, hnextVal, ?_⟩
    · unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop.body
      rw [if_pos hActiveScalar]
      simp only [bind_tc_ok, Std.lift]
      rw [hminusOne, hminusCoordinate]
      change
        (if bit != 0#u32 then
            (Slice.index_usize factors coordinate >>= fun q =>
              V7CallerCurrentReleaseR20.field.QM31.mul current q >>= fun value1 =>
                ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize)))
          else ok (cont (current, Std.Usize.wrapping_add coordinate 1#usize))) = _
      rw [if_neg hbit, hnext]
    · refine ⟨hInvariant.1, ?_⟩
      rw [hInvariant.2]
      have hbitVal : bit.val = 0 := by simpa using hbit
      simp [tensorPrefix, Finset.prod_range_succ, tensorFactor, hnextVal,
        bit, hbitVal, raw, hActive]

theorem generated_tensor_loop_corresponds
    (scale : QM31) (factors : Slice QM31) (index : Std.U32)
    (hWidth : factors.length ≤ 32)
    (hScale : GeneratedCanonicalQM31 scale)
    (hCanonical : CanonicalSlice factors) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed
        scale factors index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out = tensorPrefix scale factors index factors.length ⦄ := by
  simp only [V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed,
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_tensor_indexed_loop]
  apply loop.spec_decr_nat
    (fun state : QM31 × Std.Usize => factors.length - state.2.val)
    (fun state => state.2.val ≤ factors.length ∧
      TensorInvariant scale state.1 factors index state.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = tensorPrefix scale factors index factors.length)
  · rintro ⟨current, coordinate⟩ ⟨hLe, hInv⟩
    dsimp only at hLe hInv ⊢
    by_cases hActive : coordinate.val < factors.length
    · obtain ⟨next, out, hBody, hNext, hOut⟩ :=
        tensor_body_active scale current factors index coordinate hWidth
          hCanonical hActive hInv
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hNext]
        omega
      · rw [hNext]
        simpa [hNext] using hOut
      · rw [hNext]
        omega
    · have hEnd : coordinate.val = factors.length := by omega
      rw [tensor_body_done factors index current coordinate hActive]
      simpa [hEnd, TensorInvariant] using hInv
  · exact ⟨by norm_num, hScale, by simp [tensorPrefix]⟩

#print axioms generated_tensor_loop_corresponds

end V7CallerCurrentReleaseTensorLoop
