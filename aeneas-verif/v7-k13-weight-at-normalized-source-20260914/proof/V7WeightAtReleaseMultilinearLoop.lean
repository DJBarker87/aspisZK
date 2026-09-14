import V7WeightAtReleaseFieldBridge

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators

namespace V7WeightAtReleaseMultilinearLoop

open V7WeightAtReleaseFieldBridge

abbrev QM31 := V7WeightAtRelease.field.QM31
abbrev ExactQM31 := V7WeightAtReleaseFieldBridge.ExactQM31
instance : Inhabited QM31 := ⟨V7WeightAtRelease.field.QM31.ZERO⟩

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
      (UScalar.cast .U32 (usizeOfNatTruncate (width - 1 - coordinate)))) &&& 1#u32

def multilinearFactor (point : Slice QM31) (index : Std.U32)
    (coordinate : Nat) : ExactQM31 :=
  if selectedBit point.length index coordinate = 0#u32 then
    1 - generatedQm31ToExact point.val[coordinate]!
  else generatedQm31ToExact point.val[coordinate]!

def multilinearPrefix (scale : QM31) (point : Slice QM31)
    (index : Std.U32) (processed : Nat) : ExactQM31 :=
  generatedQm31ToExact scale *
    ∏ coordinate ∈ Finset.range processed,
      multilinearFactor point index coordinate

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
  rw [Std.Usize.wrapping_add_val_eq, usizeOfNatTruncate_val_eq]
  · apply Nat.mod_eq_of_lt
    have hsize : 0 < UScalar.size .Usize := by simp [UScalar.size_def]
    have hone : (1#usize).val = 1 := by norm_num
    omega
  · omega

private theorem usize_wrapping_sub_eq (left right : Std.Usize)
    (hLe : right.val ≤ left.val) :
    Std.Usize.wrapping_sub left right = usizeOfNatTruncate (left.val - right.val) := by
  have hLeft : left.val < UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact left.bv.isLt
  have hDiff : left.val - right.val < UScalar.size .Usize := by omega
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_sub_val_eq, usizeOfNatTruncate_val_eq hDiff]
  have hRearrange : left.val + (UScalar.size .Usize - right.val) =
      (left.val - right.val) + UScalar.size .Usize := by omega
  rw [hRearrange, Nat.add_mod_right, Nat.mod_eq_of_lt hDiff]

def MultilinearInvariant (scale current : QM31) (point : Slice QM31)
    (index : Std.U32) (coordinate : Nat) : Prop :=
  GeneratedCanonicalQM31 current ∧
    generatedQm31ToExact current = multilinearPrefix scale point index coordinate

private theorem body_done (point : Slice QM31) (index : Std.U32)
    (current : QM31) (coordinate : Std.Usize)
    (hDone : ¬ coordinate.val < point.length) :
    V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop.body
      point index current coordinate = ok (done current) := by
  unfold V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop.body
  simp [hDone]

private theorem body_active (scale current : QM31) (point : Slice QM31)
    (index : Std.U32) (coordinate : Std.Usize)
    (hWidth : point.length ≤ 32) (hCanonical : CanonicalSlice point)
    (hActive : coordinate.val < point.length)
    (hInvariant : MultilinearInvariant scale current point index coordinate.val) :
    ∃ next out,
      V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop.body
        point index current coordinate = ok (cont (out, next)) ∧
      next.val = coordinate.val + 1 ∧
      MultilinearInvariant scale out point index next.val := by
  let raw := point.val[coordinate.val]!
  have hread : Slice.index_usize point coordinate = ok raw :=
    slice_index_run point coordinate hActive
  have hrawCanonical : GeneratedCanonicalQM31 raw := hCanonical coordinate.val hActive
  let bit := selectedBit point.length index coordinate.val
  have hshiftBound : point.length - 1 - coordinate.val < 32 := by omega
  have hUsizeLarge : 32 < UScalar.size .Usize := by
    rw [UScalar.size_def, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  have hlenVal : (Slice.len point).val = point.length := by simp
  have hminusOne : Std.Usize.wrapping_sub (Slice.len point) 1#usize =
      usizeOfNatTruncate (point.length - 1) := by
    have hPositive : 1 ≤ point.length := by omega
    simpa [hlenVal] using usize_wrapping_sub_eq (Slice.len point) 1#usize (by
      simpa [hlenVal] using hPositive)
  have hminusOneVal :
      (usizeOfNatTruncate (point.length - 1)).val = point.length - 1 :=
    usizeOfNatTruncate_val_eq (by omega)
  have hminusCoordinate :
      Std.Usize.wrapping_sub (usizeOfNatTruncate (point.length - 1)) coordinate =
        usizeOfNatTruncate (point.length - 1 - coordinate.val) := by
    have h := usize_wrapping_sub_eq (usizeOfNatTruncate (point.length - 1)) coordinate (by
      rw [hminusOneVal]
      omega)
    simpa [hminusOneVal] using h
  let next := usizeOfNatTruncate (coordinate.val + 1)
  have hnext : Std.Usize.wrapping_add coordinate 1#usize = next :=
    usize_succ_run coordinate (by omega)
  have hnextVal : next.val = coordinate.val + 1 :=
    usizeOfNatTruncate_val_eq (by omega)
  have hActiveScalar : coordinate < Slice.len point := by simpa [hlenVal] using hActive
  by_cases hbit : bit = 0#u32
  · have hOneCanonical :
        GeneratedCanonicalQM31 V7WeightAtRelease.field.QM31.ONE := by
      norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
        AspisAeneasCM31Multiplicative.CanonicalRawM31,
        V7WeightAtRelease.field.QM31.ONE]
    obtain ⟨factor, hfactor, hfactorCanonical, hfactorExact⟩ :=
      generated_qm31_sub_corresponds V7WeightAtRelease.field.QM31.ONE raw
        hOneCanonical hrawCanonical
    obtain ⟨out, hout, houtCanonical, houtExact⟩ :=
      generated_qm31_mul_corresponds current factor hInvariant.1 hfactorCanonical
    refine ⟨next, out, ?_, hnextVal, ⟨houtCanonical, ?_⟩⟩
    · unfold V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop.body
      rw [if_pos hActiveScalar]
      simp only [bind_tc_ok, Std.lift]
      rw [hminusOne, hminusCoordinate]
      change
        (Slice.index_usize point coordinate >>= fun z =>
          if bit = 0#u32 then
              V7WeightAtRelease.field.QM31.sub V7WeightAtRelease.field.QM31.ONE z >>= fun q =>
                V7WeightAtRelease.field.QM31.mul current q >>= fun value1 =>
                  ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize))
          else
            V7WeightAtRelease.field.QM31.mul current z >>= fun value1 =>
              ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize))) = _
      rw [hread]
      simp only [bind_tc_ok, if_pos hbit]
      rw [hfactor]
      simp only [bind_tc_ok]
      rw [hout]
      simp only [bind_tc_ok]
      rw [hnext]
    · rw [houtExact, hfactorExact, hInvariant.2]
      have hOneExact :
          generatedQm31ToExact V7WeightAtRelease.field.QM31.ONE = 1 := by
        apply QuadraticAlgebra.ext
        · apply QuadraticAlgebra.ext <;>
            norm_num [generatedQm31ToExact, generatedCm31ToExact,
              V7WeightAtRelease.field.QM31.ONE, QuadraticAlgebra.re_one,
              QuadraticAlgebra.im_one]
        · apply QuadraticAlgebra.ext <;>
            norm_num [generatedQm31ToExact, generatedCm31ToExact,
              V7WeightAtRelease.field.QM31.ONE, QuadraticAlgebra.re_one,
              QuadraticAlgebra.im_one]
      rw [hOneExact]
      simp [multilinearPrefix, Finset.prod_range_succ, multilinearFactor, hbit,
        bit, hnextVal, raw, hActive]
      ring
  · obtain ⟨out, hout, houtCanonical, houtExact⟩ :=
      generated_qm31_mul_corresponds current raw hInvariant.1 hrawCanonical
    refine ⟨next, out, ?_, hnextVal, ⟨houtCanonical, ?_⟩⟩
    · unfold V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop.body
      rw [if_pos hActiveScalar]
      simp only [bind_tc_ok, Std.lift]
      rw [hminusOne, hminusCoordinate]
      change
        (Slice.index_usize point coordinate >>= fun z =>
          if bit = 0#u32 then
              V7WeightAtRelease.field.QM31.sub V7WeightAtRelease.field.QM31.ONE z >>= fun q =>
                V7WeightAtRelease.field.QM31.mul current q >>= fun value1 =>
                  ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize))
          else
            V7WeightAtRelease.field.QM31.mul current z >>= fun value1 =>
              ok (cont (value1, Std.Usize.wrapping_add coordinate 1#usize))) = _
      rw [hread]
      simp only [bind_tc_ok, if_neg hbit]
      rw [hout]
      simp only [bind_tc_ok]
      rw [hnext]
    · rw [houtExact, hInvariant.2]
      simp [multilinearPrefix, Finset.prod_range_succ, multilinearFactor, hbit,
        bit, hnextVal, raw, hActive]
      ring

theorem generated_multilinear_loop_corresponds
    (scale : QM31) (point : Slice QM31) (index : Std.U32)
    (hWidth : point.length ≤ 32) (hScale : GeneratedCanonicalQM31 scale)
    (hCanonical : CanonicalSlice point) :
    V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed
        scale point index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out = multilinearPrefix scale point index point.length ⦄ := by
  simp only [V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed,
    V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at_multilinear_indexed_loop]
  apply loop.spec_decr_nat
    (fun state : QM31 × Std.Usize => point.length - state.2.val)
    (fun state => state.2.val ≤ point.length ∧
      MultilinearInvariant scale state.1 point index state.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = multilinearPrefix scale point index point.length)
  · rintro ⟨current, coordinate⟩ ⟨hLe, hInv⟩
    dsimp only at hLe hInv ⊢
    by_cases hActive : coordinate.val < point.length
    · obtain ⟨next, out, hBody, hNext, hOut⟩ := body_active scale current point index
        coordinate hWidth hCanonical hActive hInv
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hNext]; omega
      · rw [hNext]; simpa [hNext] using hOut
      · rw [hNext]; omega
    · have hEnd : coordinate.val = point.length := by omega
      rw [body_done point index current coordinate hActive]
      simpa [hEnd, MultilinearInvariant] using hInv
  · exact ⟨by norm_num, hScale, by simp [multilinearPrefix]⟩

#print axioms generated_multilinear_loop_corresponds

end V7WeightAtReleaseMultilinearLoop
