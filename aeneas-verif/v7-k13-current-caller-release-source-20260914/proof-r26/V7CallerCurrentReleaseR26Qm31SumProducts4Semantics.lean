import V7CallerCurrentReleaseR26PreparedSum3Semantics

/-!
# Exact four-product QM31 sum for the current R26 verifier

The terminal line path uses the small generated Karatsuba accumulator on four
QM31 pairs.  This file proves its source loops symbolically, including the
U64 no-wrap bound, and relates the reconstructed result to the exact dot.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31SumProducts4Semantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSum3Semantics

abbrev RawM31 := field.M31
abbrev RawCM31 := field.CM31
abbrev RawQM31 := field.QM31
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

abbrev u64Cardinality : Nat := 2 ^ 64

def rowCell (row : Array Std.U64 3#usize) (channel : Nat) : Std.U64 :=
  row.val[channel]!

def matrixCell
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (component channel : Nat) : Std.U64 :=
  rowCell sums.val[component]! channel

def channelM31
    (components : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Nat) : RawM31 :=
  components.val[component]!.val[channel]!

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, hbang] using run

private theorem arrayIndexMutRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_mut_usize values index =
      ok (values.val[index.val]!, values.set index) := by
  obtain ⟨result, run, post⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_mut_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  rcases result with ⟨value, back⟩
  rcases post with ⟨valueEq, backEq⟩
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have hbang : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp
  simpa [valueEq, backEq, hbang] using run

private theorem arrayUpdateRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨out, run, outEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [outEq] using run

def accumulatedRawChannelValue
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_add
    (matrixCell sums component.val channel.val)
    (Std.U64.wrapping_mul
      (UScalar.cast .U64
        (channelM31 leftComponents component.val channel.val))
      (UScalar.cast .U64
        (channelM31 rightComponents component.val channel.val)))

def accumulateRawChannel
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) :
    Array (Array Std.U64 3#usize) 3#usize :=
  sums.set component
    ((sums.val[component.val]!).set channel
      (accumulatedRawChannelValue sums leftComponents rightComponents
        component channel))

def RawChannelUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row = component ∧ channel < processed then
        (matrixCell base row channel).val +
          (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val
      else (matrixCell base row channel).val

private theorem u32ChannelProductNoWrap (left right : RawM31) :
    (Std.U64.wrapping_mul (UScalar.cast .U64 left)
      (UScalar.cast .U64 right)).val = left.val * right.val := by
  rw [Std.U64.wrapping_mul_val_eq,
    U32.cast_U64_val_eq, U32.cast_U64_val_eq]
  have hl := UScalar.hBounds left
  have hr := UScalar.hBounds right
  have hproduct : left.val * right.val < UScalar.size .U64 := by
    rw [UScalar.size, UScalarTy.U64_numBits_eq]
    norm_num at hl hr ⊢
    nlinarith
  exact Nat.mod_eq_of_lt hproduct

private theorem accumulatedRawChannelValueNoWrap
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hbound :
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    (accumulatedRawChannelValue base leftComponents rightComponents
      component channel).val =
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val := by
  unfold accumulatedRawChannelValue
  rw [Std.U64.wrapping_add_val_eq, u32ChannelProductNoWrap]
  have hsize : UScalar.size .U64 = u64Cardinality := by
    simpa [u64Cardinality, AspisAeneasM31ReduceU64.u64Cardinality] using
      AspisAeneasM31ReduceU64.u64_size_eq
  rw [hsize, Nat.mod_eq_of_lt hbound]

private theorem matrixCellAccumulateRawSame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3) :
    matrixCell (accumulateRawChannel sums leftComponents rightComponents
      component channel) component.val channel.val =
      accumulatedRawChannelValue sums leftComponents rightComponents
        component channel := by
  unfold matrixCell rowCell accumulateRawChannel
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hcomponent, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hchannel, rfl⟩)]

private theorem matrixCellAccumulateRawFrame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) (row column : Nat)
    (hrow : row < 3) (_hcolumn : column < 3)
    (hdifferent : row ≠ component.val ∨ column ≠ channel.val) :
    matrixCell (accumulateRawChannel sums leftComponents rightComponents
      component channel) row column = matrixCell sums row column := by
  unfold matrixCell rowCell accumulateRawChannel
  simp only [Array.set_val_eq]
  by_cases hsameRow : row = component.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using hrow, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem rawChannelUpdateInvariantStep
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3)
    (hinvariant : RawChannelUpdateInvariant base current leftComponents
      rightComponents component.val channel.val)
    (hnoOverflow :
      (matrixCell base component.val channel.val).val +
        (channelM31 leftComponents component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    RawChannelUpdateInvariant base
      (accumulateRawChannel current leftComponents rightComponents
        component channel)
      leftComponents rightComponents component.val (channel.val + 1) := by
  intro row hrow column hcolumn
  by_cases hsameRow : row = component.val
  · by_cases hsameColumn : column = channel.val
    · subst row
      subst column
      rw [matrixCellAccumulateRawSame current leftComponents rightComponents
        component channel hcomponent hchannel]
      have hold := hinvariant component.val hcomponent channel.val hchannel
      simp at hold
      rw [accumulatedRawChannelValueNoWrap current leftComponents
        rightComponents component channel]
      · rw [hold]
        simp
      · rw [hold]
        exact hnoOverflow
    · rw [matrixCellAccumulateRawFrame current leftComponents rightComponents
        component channel row column hrow hcolumn (Or.inr hsameColumn)]
      have hold := hinvariant row hrow column hcolumn
      rw [hold]
      simp only [hsameRow, true_and]
      by_cases hbefore : column < channel.val
      · rw [if_pos hbefore, if_pos (by omega)]
      · rw [if_neg hbefore, if_neg (by omega)]
  · rw [matrixCellAccumulateRawFrame current leftComponents rightComponents
      component channel row column hrow hcolumn (Or.inl hsameRow)]
    have hold := hinvariant row hrow column hcolumn
    rw [hold]
    simp [hsameRow]

private theorem generatedRawChannelBodyActive
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hcomponent : component.val < 3)
    (hactive : iter.start.val < iter.end.val) (hend : iter.end.val = 3) :
    ∃ iter',
      field.qm31_accumulate_product_channels_loop0_loop0.body
          leftComponents rightComponents component iter sums =
        ok (cont (iter', accumulateRawChannel sums leftComponents
          rightComponents component iter.start)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter hactive
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have hchannel : iter.start.val < 3 := by omega
  have hleftRow := arrayIndexRun leftComponents component hcomponent
  have hleftCell := arrayIndexRun
    leftComponents.val[component.val]! iter.start hchannel
  have hrightRow := arrayIndexRun rightComponents component hcomponent
  have hrightCell := arrayIndexRun
    rightComponents.val[component.val]! iter.start hchannel
  have hsumsRow := arrayIndexRun sums component hcomponent
  have hsumsCell := arrayIndexRun sums.val[component.val]!
    iter.start hchannel
  have hsumsMut := arrayIndexMutRun sums component hcomponent
  have hrowUpdate := arrayUpdateRun sums.val[component.val]! iter.start
    (accumulatedRawChannelValue sums leftComponents rightComponents
      component iter.start) hchannel
  refine ⟨iter', ?_, startEq, congrArg UScalar.val endEq⟩
  unfold field.qm31_accumulate_product_channels_loop0_loop0.body
  rw [nextRun]
  simp only [hleftRow, hleftCell, hrightRow, hrightCell,
    hsumsRow, hsumsCell, hsumsMut, bind_tc_ok, Std.lift]
  have hvalue :
      sums.val[component.val]!.val[iter.start.val]!.wrapping_add
          (Std.U64.wrapping_mul
            (UScalar.cast .U64
              leftComponents.val[component.val]!.val[iter.start.val]!)
            (UScalar.cast .U64
              rightComponents.val[component.val]!.val[iter.start.val]!)) =
        accumulatedRawChannelValue sums leftComponents rightComponents
          component iter.start := by
    simp [accumulatedRawChannelValue, matrixCell, rowCell, channelM31]
  rw [hvalue, hrowUpdate]
  rfl

theorem generated_raw_channel_loop_corresponds
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (component : Std.Usize) (hcomponent : component.val < 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (matrixCell base component.val channel).val +
        (channelM31 leftComponents component.val channel).val *
        (channelM31 rightComponents component.val channel).val <
          u64Cardinality) :
    field.qm31_accumulate_product_channels_loop0_loop0
        { start := 0#usize, «end» := 3#usize } base leftComponents
          rightComponents component
      ⦃ out => RawChannelUpdateInvariant base out leftComponents
        rightComponents component.val 3 ⦄ := by
  simp only [field.qm31_accumulate_product_channels_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      RawChannelUpdateInvariant base state.2 leftComponents
        rightComponents component.val state.1.start.val)
    (fun out => RawChannelUpdateInvariant base out leftComponents
      rightComponents component.val 3)
  · rintro ⟨iter, current⟩ ⟨hend, hstart, hinvariant⟩
    dsimp only at hend hstart hinvariant ⊢
    by_cases hactive : iter.start.val < iter.end.val
    · obtain ⟨iter', hbody, hnextStart, hnextEnd⟩ :=
        generatedRawChannelBodyActive leftComponents rightComponents
          component iter current hcomponent hactive hend
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hnextEnd]
        exact hend
      · rw [hnextStart]
        omega
      · rw [hnextStart]
        apply rawChannelUpdateInvariantStep base current leftComponents
          rightComponents component iter.start hcomponent (by omega)
          hinvariant
        exact hnoOverflow iter.start.val (by omega)
      · rw [hnextStart]
        omega
    · have hdone : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold field.qm31_accumulate_product_channels_loop0_loop0.body
      rw [nextRun]
      simpa [hdone] using hinvariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro row hrow channel hchannel
    simp

def RawComponentUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row < processed then
        (matrixCell base row channel).val +
          (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val
      else (matrixCell base row channel).val

private theorem rawComponentUpdateInvariantStep
    (base current out : Array (Array Std.U64 3#usize) 3#usize)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component : Std.Usize) (_hcomponent : component.val < 3)
    (houter : RawComponentUpdateInvariant base current leftComponents
      rightComponents component.val)
    (hinner : RawChannelUpdateInvariant current out leftComponents
      rightComponents component.val 3) :
    RawComponentUpdateInvariant base out leftComponents rightComponents
      (component.val + 1) := by
  intro row hrow channel hchannel
  have hinnerCell := hinner row hrow channel hchannel
  have houterCell := houter row hrow channel hchannel
  by_cases hsame : row = component.val
  · subst row
    simp at houterCell
    simp [houterCell, hchannel] at hinnerCell
    simpa using hinnerCell
  · have hframe : (matrixCell out row channel).val =
        (matrixCell current row channel).val := by
      simpa [hsame] using hinnerCell
    rw [hframe, houterCell]
    by_cases hbefore : row < component.val
    · rw [if_pos hbefore, if_pos (by omega)]
    · rw [if_neg hbefore, if_neg (by omega)]

private theorem generatedRawComponentBodyActive
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hactive : iter.start.val < iter.end.val) (hend : iter.end.val = 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (matrixCell current iter.start.val channel).val +
        (channelM31 leftComponents iter.start.val channel).val *
        (channelM31 rightComponents iter.start.val channel).val <
          u64Cardinality) :
    ∃ iter' out,
      field.qm31_accumulate_product_channels_loop0.body
          leftComponents rightComponents iter current = ok (cont (iter', out)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      RawChannelUpdateInvariant current out leftComponents
        rightComponents iter.start.val 3 := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter hactive
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have hcomponent : iter.start.val < 3 := by omega
  have innerSpec := generated_raw_channel_loop_corresponds
    leftComponents rightComponents current iter.start hcomponent hnoOverflow
  obtain ⟨out, innerRun, innerPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists innerSpec
  refine ⟨iter', out, ?_, startEq, congrArg UScalar.val endEq, innerPost⟩
  unfold field.qm31_accumulate_product_channels_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  rw [innerRun]
  rfl

theorem generated_raw_component_loop_corresponds
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (hnoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell base row channel).val +
        (channelM31 leftComponents row channel).val *
        (channelM31 rightComponents row channel).val < u64Cardinality) :
    field.qm31_accumulate_product_channels_loop0
        { start := 0#usize, «end» := 3#usize } base leftComponents
          rightComponents
      ⦃ out => RawComponentUpdateInvariant base out leftComponents
        rightComponents 3 ⦄ := by
  simp only [field.qm31_accumulate_product_channels_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      RawComponentUpdateInvariant base state.2 leftComponents
        rightComponents state.1.start.val)
    (fun out => RawComponentUpdateInvariant base out leftComponents
      rightComponents 3)
  · rintro ⟨iter, current⟩ ⟨hend, hstart, hinvariant⟩
    dsimp only at hend hstart hinvariant ⊢
    by_cases hactive : iter.start.val < iter.end.val
    · have hcomponent : iter.start.val < 3 := by omega
      have hcurrentNoOverflow : ∀ channel, channel < 3 →
          (matrixCell current iter.start.val channel).val +
            (channelM31 leftComponents iter.start.val channel).val *
            (channelM31 rightComponents iter.start.val channel).val <
              u64Cardinality := by
        intro channel hchannel
        have hcurrent := hinvariant iter.start.val hcomponent channel hchannel
        rw [if_neg (by omega)] at hcurrent
        rw [hcurrent]
        exact hnoOverflow iter.start.val hcomponent channel hchannel
      obtain ⟨iter', out, hbody, hnextStart, hnextEnd, hinner⟩ :=
        generatedRawComponentBodyActive leftComponents rightComponents
          iter current hactive hend hcurrentNoOverflow
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hnextEnd]
        exact hend
      · rw [hnextStart]
        omega
      · rw [hnextStart]
        exact rawComponentUpdateInvariantStep base current out
          leftComponents rightComponents iter.start hcomponent
          hinvariant hinner
      · rw [hnextStart]
        omega
    · have hdone : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold field.qm31_accumulate_product_channels_loop0.body
      rw [nextRun]
      simpa [hdone] using hinvariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro row hrow channel hchannel
    simp

def generatedComponentMatrix
    (q : RawQM31) (qsum : RawCM31) (m0 m1 m2 : RawM31) :
    Array (Array RawM31 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [q.c0.a, q.c0.b, m0],
    Array.make 3#usize [q.c1.a, q.c1.b, m1],
    Array.make 3#usize [qsum.a, qsum.b, m2]]

def CanonicalChannelMatrix
    (components : Array (Array RawM31 3#usize) 3#usize) : Prop :=
  ∀ component, component < 3 → ∀ channel, channel < 3 →
    AspisAeneasCM31Multiplicative.CanonicalRawM31
      (channelM31 components component channel).val

private theorem generatedComponentMatrixCanonical
    (q : RawQM31) (qsum : RawCM31) (m0 m1 m2 : RawM31)
    (hq : GeneratedCanonicalQM31 q) (hqsum : GeneratedCanonicalCM31 qsum)
    (hm0 : AspisAeneasCM31Multiplicative.CanonicalRawM31 m0.val)
    (hm1 : AspisAeneasCM31Multiplicative.CanonicalRawM31 m1.val)
    (hm2 : AspisAeneasCM31Multiplicative.CanonicalRawM31 m2.val) :
    CanonicalChannelMatrix (generatedComponentMatrix q qsum m0 m1 m2) := by
  rcases hq with ⟨⟨hc0a, hc0b⟩, ⟨hc1a, hc1b⟩⟩
  rcases hqsum with ⟨hsuma, hsumb⟩
  intro component hcomponent channel hchannel
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals simp only [channelM31, generatedComponentMatrix, Array.make]
  all_goals assumption

private theorem generatedComponentMatrixExact
    (q : RawQM31) (qsum : RawCM31) (m0 m1 m2 : RawM31)
    (hqsumExact : generatedCm31ToExact qsum =
      generatedCm31ToExact q.c0 + generatedCm31ToExact q.c1)
    (hm0Exact : ((m0.val : Nat) : ExactM31) =
      (q.c0.a.val : ExactM31) + (q.c0.b.val : ExactM31))
    (hm1Exact : ((m1.val : Nat) : ExactM31) =
      (q.c1.a.val : ExactM31) + (q.c1.b.val : ExactM31))
    (hm2Exact : ((m2.val : Nat) : ExactM31) =
      (qsum.a.val : ExactM31) + (qsum.b.val : ExactM31)) :
    ∀ component, component < 3 → ∀ channel, channel < 3 →
      (((channelM31 (generatedComponentMatrix q qsum m0 m1 m2)
        component channel).val : Nat) : ExactM31) =
        exactInputChannel (generatedQm31ToExact q) component channel := by
  intro component hcomponent channel hchannel
  have hsumRe := congrArg (fun x :
    V7CallerCurrentReleaseR26FieldBridge.ExactCM31 => x.re) hqsumExact
  have hsumIm := congrArg (fun x :
    V7CallerCurrentReleaseR26FieldBridge.ExactCM31 => x.im) hqsumExact
  change ((qsum.a.val : ExactM31) =
    (q.c0.a.val : ExactM31) + (q.c1.a.val : ExactM31)) at hsumRe
  change ((qsum.b.val : ExactM31) =
    (q.c0.b.val : ExactM31) + (q.c1.b.val : ExactM31)) at hsumIm
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals simp only [channelM31, generatedComponentMatrix, Array.make]
  all_goals simp [exactInputChannel, exactQMComponent, exactCMChannel,
    generatedQm31ToExact, generatedCm31ToExact] at hqsumExact ⊢
  all_goals try exact hm0Exact
  all_goals try exact hm1Exact
  all_goals try rw [hm2Exact]
  all_goals try rw [hsumRe]
  all_goals try rw [hsumIm]

def SingleProductPost
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : RawQM31) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell after row channel).val ≤
        (matrixCell before row channel).val + channelProductBound ∧
    (((matrixCell after row channel).val : Nat) : ExactM31) =
      (((matrixCell before row channel).val : Nat) : ExactM31) +
        exactInputChannel (generatedQm31ToExact left) row channel *
          exactInputChannel (generatedQm31ToExact right) row channel

private theorem rawComponentPostToSingleProduct
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : RawQM31)
    (leftComponents rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (hleftCanonical : CanonicalChannelMatrix leftComponents)
    (hrightCanonical : CanonicalChannelMatrix rightComponents)
    (hleftExact : ∀ component, component < 3 →
      ∀ channel, channel < 3 →
        (((channelM31 leftComponents component channel).val : Nat) :
          ExactM31) =
          exactInputChannel (generatedQm31ToExact left) component channel)
    (hrightExact : ∀ component, component < 3 →
      ∀ channel, channel < 3 →
        (((channelM31 rightComponents component channel).val : Nat) :
          ExactM31) =
          exactInputChannel (generatedQm31ToExact right) component channel)
    (hpost : RawComponentUpdateInvariant before after leftComponents
      rightComponents 3) : SingleProductPost before after left right := by
  intro row hrow channel hchannel
  have hcell := hpost row hrow channel hchannel
  simp only [show row < 3 from hrow, if_pos] at hcell
  have hleftCell := hleftCanonical row hrow channel hchannel
  have hrightCell := hrightCanonical row hrow channel hchannel
  have hproduct :=
    V7CallerCurrentReleaseR26PreparedSum3Semantics.channelProductLe
      _ _ hleftCell hrightCell
  constructor
  · rw [hcell]
    exact Nat.add_le_add_left hproduct _
  · rw [hcell, Nat.cast_add, Nat.cast_mul,
      hleftExact row hrow channel hchannel,
      hrightExact row hrow channel hchannel]

theorem generated_accumulate_product_channels_corresponds
    (before : Array (Array Std.U64 3#usize) 3#usize)
    (left right : RawQM31)
    (leftCanonical : GeneratedCanonicalQM31 left)
    (rightCanonical : GeneratedCanonicalQM31 right)
    (hnoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell before row channel).val + channelProductBound <
        u64Cardinality) :
    ∃ after,
      field.qm31_accumulate_product_channels before left right = ok after ∧
      SingleProductPost before after left right := by
  obtain ⟨leftSum, leftSumRun, leftSumCanonical, leftSumExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSumSemantics.generated_cm31_add_corresponds
      left.c0 left.c1 leftCanonical.1 leftCanonical.2
  obtain ⟨rightSum, rightSumRun, rightSumCanonical, rightSumExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSumSemantics.generated_cm31_add_corresponds
      right.c0 right.c1 rightCanonical.1 rightCanonical.2
  obtain ⟨lm0, lm0Run, lm0Canonical, lm0Exact⟩ :=
    generated_m31_add_corresponds left.c0.a left.c0.b
      leftCanonical.1.1 leftCanonical.1.2
  obtain ⟨lm1, lm1Run, lm1Canonical, lm1Exact⟩ :=
    generated_m31_add_corresponds left.c1.a left.c1.b
      leftCanonical.2.1 leftCanonical.2.2
  obtain ⟨lm2, lm2Run, lm2Canonical, lm2Exact⟩ :=
    generated_m31_add_corresponds leftSum.a leftSum.b
      leftSumCanonical.1 leftSumCanonical.2
  obtain ⟨rm0, rm0Run, rm0Canonical, rm0Exact⟩ :=
    generated_m31_add_corresponds right.c0.a right.c0.b
      rightCanonical.1.1 rightCanonical.1.2
  obtain ⟨rm1, rm1Run, rm1Canonical, rm1Exact⟩ :=
    generated_m31_add_corresponds right.c1.a right.c1.b
      rightCanonical.2.1 rightCanonical.2.2
  obtain ⟨rm2, rm2Run, rm2Canonical, rm2Exact⟩ :=
    generated_m31_add_corresponds rightSum.a rightSum.b
      rightSumCanonical.1 rightSumCanonical.2
  let leftComponents := generatedComponentMatrix left leftSum lm0 lm1 lm2
  let rightComponents := generatedComponentMatrix right rightSum rm0 rm1 rm2
  have leftComponentsCanonical : CanonicalChannelMatrix leftComponents :=
    generatedComponentMatrixCanonical left leftSum lm0 lm1 lm2
      leftCanonical leftSumCanonical lm0Canonical lm1Canonical lm2Canonical
  have rightComponentsCanonical : CanonicalChannelMatrix rightComponents :=
    generatedComponentMatrixCanonical right rightSum rm0 rm1 rm2
      rightCanonical rightSumCanonical rm0Canonical rm1Canonical rm2Canonical
  have leftComponentsExact := generatedComponentMatrixExact left leftSum
    lm0 lm1 lm2 leftSumExact lm0Exact lm1Exact lm2Exact
  have rightComponentsExact := generatedComponentMatrixExact right rightSum
    rm0 rm1 rm2 rightSumExact rm0Exact rm1Exact rm2Exact
  have rawNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell before row channel).val +
        (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val < u64Cardinality := by
    intro row hrow channel hchannel
    have hproduct :=
      V7CallerCurrentReleaseR26PreparedSum3Semantics.channelProductLe
        _ _ (leftComponentsCanonical row hrow channel hchannel)
          (rightComponentsCanonical row hrow channel hchannel)
    exact lt_of_le_of_lt (Nat.add_le_add_left hproduct _)
      (hnoOverflow row hrow channel hchannel)
  have componentSpec := generated_raw_component_loop_corresponds
    leftComponents rightComponents before rawNoOverflow
  obtain ⟨after, componentRun, componentPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists componentSpec
  refine ⟨after, ?_, rawComponentPostToSingleProduct before after left right
    leftComponents rightComponents leftComponentsCanonical
    rightComponentsCanonical leftComponentsExact rightComponentsExact
    componentPost⟩
  unfold field.qm31_accumulate_product_channels
  rw [leftSumRun]
  simp only [bind_tc_ok]
  rw [rightSumRun]
  simp only [bind_tc_ok]
  rw [lm0Run]
  simp only [bind_tc_ok]
  rw [lm1Run]
  simp only [bind_tc_ok]
  rw [lm2Run]
  simp only [bind_tc_ok]
  rw [rm0Run]
  simp only [bind_tc_ok]
  rw [rm1Run]
  simp only [bind_tc_ok]
  rw [rm2Run]
  simp only [bind_tc_ok]
  change
    field.qm31_accumulate_product_channels_loop0
      { start := 0#usize, «end» := 3#usize } before leftComponents
        rightComponents = ok after
  exact componentRun

def GeneratedCanonicalQM31Array4 (values : Array RawQM31 4#usize) : Prop :=
  ∀ index, index < 4 → GeneratedCanonicalQM31 values.val[index]!

def exactChannelDot4
    (left right : Array RawQM31 4#usize) (processed row channel : Nat) :
    ExactM31 :=
  ∑ index ∈ Finset.range processed,
    exactInputChannel (generatedQm31ToExact left.val[index]!) row channel *
      exactInputChannel (generatedQm31ToExact right.val[index]!) row channel

def OuterChannelInvariant4
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (left right : Array RawQM31 4#usize) (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val ≤ processed * channelProductBound ∧
    (((matrixCell current row channel).val : Nat) : ExactM31) =
      exactChannelDot4 left right processed row channel

private theorem outerInvariantStep
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : Array RawQM31 4#usize) (processed : Nat)
    (hinvariant : OuterChannelInvariant4 before left right processed)
    (hpost : SingleProductPost before after left.val[processed]!
      right.val[processed]!) :
    OuterChannelInvariant4 after left right (processed + 1) := by
  intro row hrow channel hchannel
  have hold := hinvariant row hrow channel hchannel
  have hstep := hpost row hrow channel hchannel
  constructor
  · exact le_trans hstep.1 (by
      calc
        (matrixCell before row channel).val + channelProductBound
            ≤ processed * channelProductBound + channelProductBound :=
              Nat.add_le_add_right hold.1 _
        _ = (processed + 1) * channelProductBound := by ring)
  · rw [hstep.2, hold.2]
    simp [exactChannelDot4, Finset.sum_range_succ]

private theorem wrappingAddOneSmall
    (index : Std.Usize) (bound : index.val + 1 < Usize.size) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  exact Nat.mod_eq_of_lt bound

private theorem sumProductsBodyDone
    (left right : Array RawQM31 4#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (done : ¬ index.val < 4) :
    field.qm31_sum_products_small_loop.body left right sums index =
      ok (ControlFlow.done sums) := by
  unfold field.qm31_sum_products_small_loop.body
  rw [if_neg]
  simpa using done

private theorem sumProductsBodyActive
    (left right : Array RawQM31 4#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize)
    (leftCanonical : GeneratedCanonicalQM31Array4 left)
    (rightCanonical : GeneratedCanonicalQM31Array4 right)
    (active : index.val < 4)
    (invariant : OuterChannelInvariant4 sums left right index.val) :
    ∃ nextSums nextIndex,
      field.qm31_sum_products_small_loop.body left right sums index =
        ok (ControlFlow.cont (nextSums, nextIndex)) ∧
      nextIndex.val = index.val + 1 ∧
      OuterChannelInvariant4 nextSums left right nextIndex.val := by
  let leftValue := left.val[index.val]!
  let rightValue := right.val[index.val]!
  have leftRead := arrayIndexRun left index active
  have rightRead := arrayIndexRun right index active
  have noOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell sums row channel).val + channelProductBound <
        u64Cardinality := by
    intro row hrow channel hchannel
    have hbound := (invariant row hrow channel hchannel).1
    calc
      (matrixCell sums row channel).val + channelProductBound
          ≤ index.val * channelProductBound + channelProductBound :=
            Nat.add_le_add_right hbound _
      _ = (index.val + 1) * channelProductBound := by ring
      _ ≤ 4 * channelProductBound := by
        exact Nat.mul_le_mul_right channelProductBound (by omega)
      _ < u64Cardinality := by
        exact V7CallerCurrentReleaseR26PreparedSum3Semantics.fourChannelProductsFitU64
  obtain ⟨nextSums, accumulationRun, productPost⟩ :=
    generated_accumulate_product_channels_corresponds sums leftValue
      rightValue (leftCanonical index.val active)
      (rightCanonical index.val active) noOverflow
  let nextIndex := Std.Usize.wrapping_add index 1#usize
  have usizeBound : index.val + 1 < Usize.size := by
    have literalBound := UScalar.hSize (4#usize)
    have : 4 < Usize.size := by
      simpa [UScalar.size_UScalarTyUsize] using literalBound
    omega
  have nextVal : nextIndex.val = index.val + 1 := by
    exact wrappingAddOneSmall index usizeBound
  refine ⟨nextSums, nextIndex, ?_, nextVal, ?_⟩
  · unfold field.qm31_sum_products_small_loop.body
    rw [if_pos (by simpa using active)]
    rw [leftRead]
    simp only [bind_tc_ok]
    rw [rightRead]
    simp only [bind_tc_ok]
    change
      (do
        let sums1 ← field.qm31_accumulate_product_channels sums
          leftValue rightValue
        let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
        ok (cont (sums1, index1))) = _
    rw [accumulationRun]
    simp [Std.lift, nextIndex]
  · rw [nextVal]
    exact outerInvariantStep sums nextSums left right index.val invariant
      (by simpa [leftValue, rightValue] using productPost)

theorem generated_sum_products_loop_four_corresponds
    (left right : Array RawQM31 4#usize)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (leftCanonical : GeneratedCanonicalQM31Array4 left)
    (rightCanonical : GeneratedCanonicalQM31Array4 right)
    (initialInvariant : OuterChannelInvariant4 initial left right 0) :
    field.qm31_sum_products_small_loop left right initial 0#usize
      ⦃ out => OuterChannelInvariant4 out left right 4 ⦄ := by
  simp only [field.qm31_sum_products_small_loop]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      4 - state.2.val)
    (fun state => state.2.val ≤ 4 ∧
      OuterChannelInvariant4 state.1 left right state.2.val)
    (fun out => OuterChannelInvariant4 out left right 4)
  · rintro ⟨current, index⟩ ⟨indexLe, invariant⟩
    dsimp only at indexLe invariant ⊢
    by_cases active : index.val < 4
    · obtain ⟨nextSums, nextIndex, bodyRun, nextVal, nextInvariant⟩ :=
        sumProductsBodyActive left right current index leftCanonical
          rightCanonical active invariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, nextInvariant⟩, ?_⟩ <;> rw [nextVal] <;> omega
    · have atEnd : index.val = 4 := by omega
      rw [sumProductsBodyDone left right current index active]
      simpa [atEnd] using invariant
  · exact ⟨by norm_num, initialInvariant⟩

def zeroU64ChannelMatrix :
    Array (Array Std.U64 3#usize) 3#usize :=
  Array.repeat 3#usize (Array.repeat 3#usize 0#u64)

private theorem zeroMatrixCell
    (row channel : Nat) (hrow : row < 3) (hchannel : channel < 3) :
    matrixCell zeroU64ChannelMatrix row channel = 0#u64 := by
  have hrow' : row < (3#usize).val := by simpa using hrow
  have hchannel' : channel < (3#usize).val := by simpa using hchannel
  unfold matrixCell rowCell zeroU64ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hrow']
  rw [Array.repeat_val, List.getElem!_replicate _ hchannel']

theorem zero_outer_invariant4
    (left right : Array RawQM31 4#usize) :
    OuterChannelInvariant4 zeroU64ChannelMatrix left right 0 := by
  intro row hrow channel hchannel
  rw [zeroMatrixCell row channel hrow hchannel]
  simp [exactChannelDot4]

def exactProductDot4
    (left right : Array RawQM31 4#usize) : ExactQM31 :=
  ∑ index ∈ Finset.range 4,
    generatedQm31ToExact left.val[index]! *
      generatedQm31ToExact right.val[index]!

private theorem reconstructExactEqProductDot4
    (left right : Array RawQM31 4#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hinvariant : OuterChannelInvariant4 sums left right 4) :
    reconstructQMExact sums = exactProductDot4 left right := by
  have h00 := (hinvariant 0 (by omega) 0 (by omega)).2
  have h01 := (hinvariant 0 (by omega) 1 (by omega)).2
  have h02 := (hinvariant 0 (by omega) 2 (by omega)).2
  have h10 := (hinvariant 1 (by omega) 0 (by omega)).2
  have h11 := (hinvariant 1 (by omega) 1 (by omega)).2
  have h12 := (hinvariant 1 (by omega) 2 (by omega)).2
  have h20 := (hinvariant 2 (by omega) 0 (by omega)).2
  have h21 := (hinvariant 2 (by omega) 1 (by omega)).2
  have h22 := (hinvariant 2 (by omega) 2 (by omega)).2
  unfold matrixCell rowCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot4,
        exactChannelDot4, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        V7CallerCurrentReleaseR26PreparedSum3Semantics.rowCell,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h10, h11, h12]
      ring
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot4,
        exactChannelDot4, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        V7CallerCurrentReleaseR26PreparedSum3Semantics.rowCell,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h02, h10, h11, h12]
      ring
  · apply QuadraticAlgebra.ext
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot4,
        exactChannelDot4, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        V7CallerCurrentReleaseR26PreparedSum3Semantics.rowCell,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h10, h11, h20, h21]
      ring
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot4,
        exactChannelDot4, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        V7CallerCurrentReleaseR26PreparedSum3Semantics.rowCell,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
      ring

theorem generated_qm31_sum_products4_corresponds
    (left right : Array RawQM31 4#usize)
    (leftCanonical : GeneratedCanonicalQM31Array4 left)
    (rightCanonical : GeneratedCanonicalQM31Array4 right) :
    ∃ out,
      field.qm31_sum_products4 left right = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = exactProductDot4 left right := by
  have loopSpec := generated_sum_products_loop_four_corresponds left right
    zeroU64ChannelMatrix leftCanonical rightCanonical
      (zero_outer_invariant4 left right)
  obtain ⟨sums, loopRun, sumsInvariant⟩ :=
    Aeneas.Std.WP.spec_imp_exists loopSpec
  obtain ⟨out, reconstructionRun, outCanonical, outExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSum3Semantics.generated_reconstruction_corresponds
      sums
  refine ⟨out, ?_, outCanonical, ?_⟩
  · unfold field.qm31_sum_products4 field.qm31_sum_products_small
    unfold zeroU64ChannelMatrix at loopRun
    simp only at loopRun ⊢
    rw [loopRun]
    simp only [bind_tc_ok]
    exact reconstructionRun
  · rw [outExact]
    exact reconstructExactEqProductDot4 left right sums sumsInvariant

#print axioms generated_raw_channel_loop_corresponds
#print axioms generated_raw_component_loop_corresponds
#print axioms generated_accumulate_product_channels_corresponds
#print axioms generated_sum_products_loop_four_corresponds
#print axioms generated_qm31_sum_products4_corresponds

end V7CallerCurrentReleaseR26Qm31SumProducts4Semantics
