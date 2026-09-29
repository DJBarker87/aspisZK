import V7CallerCurrentReleaseR26PreparedSumSemantics

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000

/-!
# Exact three-product prepared accumulation for the current R26 verifier

This file proves the three-product channel loop used by the production value
fold, reusing the exact field bridge and symbolic no-overflow argument.
-/

namespace V7CallerCurrentReleaseR26PreparedSum3Semantics

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSumSemantics

abbrev RawM31 := V7CallerCurrentReleaseR26.field.M31
abbrev RawCM31 := V7CallerCurrentReleaseR26.field.CM31
abbrev RawQM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev RawPrepared := V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactCM31 := V7CallerCurrentReleaseR26FieldBridge.ExactCM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawQM31 :=
  ⟨V7CallerCurrentReleaseR26.field.QM31.ZERO⟩
local instance : Inhabited RawPrepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩

def cachedChannel
    (prepared : RawPrepared) (component channel : Nat) : RawM31 :=
  prepared.components.val[component]!.val[channel]!

def exactCMChannel (x : ExactCM31) (channel : Nat) : ExactM31 :=
  if channel = 0 then x.re else if channel = 1 then x.im else x.re + x.im

def exactQMComponent (x : ExactQM31) (component : Nat) : ExactCM31 :=
  if component = 0 then x.re
  else if component = 1 then x.im
  else x.re + x.im

def exactInputChannel
    (x : ExactQM31) (component channel : Nat) : ExactM31 :=
  exactCMChannel (exactQMComponent x component) channel

/-- Semantic view of all nine generated cache cells. -/
def PreparedFor (prepared : RawPrepared) (left : RawQM31) : Prop :=
  ∀ component, component < 3 → ∀ channel, channel < 3 →
    AspisAeneasCM31Multiplicative.CanonicalRawM31
      (cachedChannel prepared component channel).val ∧
    (((cachedChannel prepared component channel).val : Nat) : ExactM31) =
      exactInputChannel (generatedQm31ToExact left) component channel

private theorem representedRowCellExact
    (row : Array RawM31 3#usize) (x : RawCM31)
    (hx : GeneratedCanonicalCM31 x) (hrow : RepresentsPreparedRow row x)
    (channel : Nat) (hchannel : channel < 3) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31
        row.val[channel]!.val ∧
      (((row.val[channel]!).val : Nat) : ExactM31) =
        exactCMChannel (generatedCm31ToExact x) channel := by
  obtain ⟨sum, hsum, hsumCanonical, hrowVal⟩ := hrow
  obtain ⟨sumOut, hsumOut, _, hsumExact⟩ :=
    generated_m31_add_corresponds x.a x.b hx.1 hx.2
  rw [hsum] at hsumOut
  simp only [Result.ok.injEq] at hsumOut
  subst sumOut
  have hc : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · constructor
    · simpa [hrowVal] using hx.1
    · simp [hrowVal, exactCMChannel, generatedCm31ToExact]
  · constructor
    · simpa [hrowVal] using hx.2
    · simp [hrowVal, exactCMChannel, generatedCm31ToExact]
  · constructor
    · simpa [hrowVal] using hsumCanonical
    · simpa [hrowVal, exactCMChannel, generatedCm31ToExact] using hsumExact

/-- The stronger operational cache relation implies the nine-cell semantic
view used by the fused product loop. -/
theorem representsPrepared_implies_preparedFor
    (prepared : RawPrepared) (left : RawQM31)
    (hprepared : RepresentsPrepared prepared left)
    (hleft : GeneratedCanonicalQM31 left) : PreparedFor prepared left := by
  obtain ⟨leftSum, row0, row1, row2, hleftSum, hleftSumCanonical,
      hrow0, hrow1, hrow2, hcomponents⟩ := hprepared
  obtain ⟨leftSumOut, hleftSumOut, _, hleftSumExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSumSemantics.generated_cm31_add_corresponds
      left.c0 left.c1 hleft.1 hleft.2
  rw [hleftSum] at hleftSumOut
  simp only [Result.ok.injEq] at hleftSumOut
  subst leftSumOut
  intro component hcomponent channel hchannel
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · have hcell := representedRowCellExact row0 left.c0 hleft.1 hrow0
      channel hchannel
    simpa [cachedChannel, hcomponents, exactInputChannel,
      exactQMComponent, generatedQm31ToExact, generatedCm31ToExact] using hcell
  · have hcell := representedRowCellExact row1 left.c1 hleft.2 hrow1
      channel hchannel
    simpa [cachedChannel, hcomponents, exactInputChannel,
      exactQMComponent, generatedQm31ToExact, generatedCm31ToExact] using hcell
  · have hcell := representedRowCellExact row2 leftSum
      hleftSumCanonical hrow2 channel hchannel
    rcases hcell with ⟨hcanonical, hexact⟩
    refine ⟨by simpa [cachedChannel, hcomponents] using hcanonical, ?_⟩
    have hexact' :
        (((cachedChannel prepared 2 channel).val : Nat) : ExactM31) =
          exactCMChannel (generatedCm31ToExact leftSum) channel := by
      simpa [cachedChannel, hcomponents] using hexact
    rw [hleftSumExact] at hexact'
    simpa [exactInputChannel, exactQMComponent, generatedQm31ToExact,
      generatedCm31ToExact] using hexact'

abbrev m31Modulus : Nat := 2147483647
abbrev channelProductBound : Nat := (m31Modulus - 1) ^ 2
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

private theorem listGetBangEq
    {T : Type} [Inhabited T] (values : List T) (index : Nat)
    (hindex : index < values.length) : values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem arrayIndexRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  simpa [valueEq, listGetBangEq values.val index.val hbound] using run

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
  simpa [valueEq, backEq, listGetBangEq values.val index.val hbound] using run

private theorem arrayUpdateRun
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (value : T)
    (hindex : index.val < N.val) :
    Array.update values index value = ok (values.set index value) := by
  obtain ⟨out, run, outEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.update_spec values index value (by
      simpa [Array.length_eq] using hindex))
  simpa [outEq] using run

def accumulatedChannelValue
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) : Std.U64 :=
  Std.U64.wrapping_add
    (matrixCell sums component.val channel.val)
    (Std.U64.wrapping_mul
      (UScalar.cast .U64 (cachedChannel prepared component.val channel.val))
      (UScalar.cast .U64
        (channelM31 rightComponents component.val channel.val)))

def accumulateChannel
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) :
    Array (Array Std.U64 3#usize) 3#usize :=
  sums.set component
    ((sums.val[component.val]!).set channel
      (accumulatedChannelValue sums prepared rightComponents
        component channel))

def ChannelUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row = component ∧ channel < processed then
        (matrixCell base row channel).val +
          (cachedChannel prepared row channel).val *
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

private theorem accumulatedChannelValueNoWrap
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hbound :
      (matrixCell base component.val channel.val).val +
        (cachedChannel prepared component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    (accumulatedChannelValue base prepared rightComponents
      component channel).val =
      (matrixCell base component.val channel.val).val +
        (cachedChannel prepared component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val := by
  unfold accumulatedChannelValue
  rw [Std.U64.wrapping_add_val_eq, u32ChannelProductNoWrap]
  have hsize : UScalar.size .U64 = u64Cardinality := by
    simpa [u64Cardinality, AspisAeneasM31ReduceU64.u64Cardinality] using
      AspisAeneasM31ReduceU64.u64_size_eq
  rw [hsize, Nat.mod_eq_of_lt hbound]

private theorem matrixCellAccumulateSame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3) :
    matrixCell (accumulateChannel sums prepared rightComponents
      component channel) component.val channel.val =
      accumulatedChannelValue sums prepared rightComponents
        component channel := by
  unfold matrixCell rowCell accumulateChannel
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hcomponent, rfl⟩)]
  simp only [Array.set_val_eq]
  rw [List.set_getElem!_eq _ _ _ _ (by
    exact ⟨by simpa [Array.length_eq] using hchannel, rfl⟩)]

private theorem matrixCellAccumulateFrame
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize) (row column : Nat)
    (hrow : row < 3) (_hcolumn : column < 3)
    (hdifferent : row ≠ component.val ∨ column ≠ channel.val) :
    matrixCell (accumulateChannel sums prepared rightComponents
      component channel) row column = matrixCell sums row column := by
  unfold matrixCell rowCell accumulateChannel
  simp only [Array.set_val_eq]
  by_cases hsameRow : row = component.val
  · subst row
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using hrow, rfl⟩)]
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne _ _ _ _ (by omega)]
  · rw [List.set_getElem!_ne _ _ _ _ (by omega)]

private theorem channelUpdateInvariantStep
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component channel : Std.Usize)
    (hcomponent : component.val < 3) (hchannel : channel.val < 3)
    (hinvariant : ChannelUpdateInvariant base current prepared
      rightComponents component.val channel.val)
    (hnoOverflow :
      (matrixCell base component.val channel.val).val +
        (cachedChannel prepared component.val channel.val).val *
        (channelM31 rightComponents component.val channel.val).val <
          u64Cardinality) :
    ChannelUpdateInvariant base
      (accumulateChannel current prepared rightComponents component channel)
      prepared rightComponents component.val (channel.val + 1) := by
  intro row hrow column hcolumn
  by_cases hsameRow : row = component.val
  · by_cases hsameColumn : column = channel.val
    · subst row
      subst column
      rw [matrixCellAccumulateSame current prepared rightComponents
        component channel hcomponent hchannel]
      have hold := hinvariant component.val hcomponent channel.val hchannel
      simp at hold
      rw [accumulatedChannelValueNoWrap current prepared rightComponents
        component channel]
      · rw [hold]
        simp
      · rw [hold]
        exact hnoOverflow
    · rw [matrixCellAccumulateFrame current prepared rightComponents
        component channel row column hrow hcolumn (Or.inr hsameColumn)]
      have hold := hinvariant row hrow column hcolumn
      rw [hold]
      simp only [hsameRow, true_and]
      by_cases hbefore : column < channel.val
      · rw [if_pos hbefore, if_pos (by omega)]
      · rw [if_neg hbefore, if_neg (by omega)]
  · rw [matrixCellAccumulateFrame current prepared rightComponents
      component channel row column hrow hcolumn (Or.inl hsameRow)]
    have hold := hinvariant row hrow column hcolumn
    rw [hold]
    simp [hsameRow]

private theorem generatedChannelBodyActive
    (left : Array RawPrepared 3#usize) (index : Std.Usize)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hindex : index.val < 3) (hcomponent : component.val < 3)
    (hactive : iter.start.val < iter.end.val) (hend : iter.end.val = 3) :
    ∃ iter',
      V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0.body
          left index rightComponents component iter sums =
        ok (cont (iter', accumulateChannel sums left.val[index.val]!
          rightComponents component iter.start)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter hactive
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have hchannel : iter.start.val < 3 := by omega
  have hleft := arrayIndexRun left index hindex
  have hleftRow := arrayIndexRun left.val[index.val]!.components
    component hcomponent
  have hleftCell := arrayIndexRun
    left.val[index.val]!.components.val[component.val]! iter.start hchannel
  have hrightRow := arrayIndexRun rightComponents component hcomponent
  have hrightCell := arrayIndexRun
    rightComponents.val[component.val]! iter.start hchannel
  have hsumsRow := arrayIndexRun sums component hcomponent
  have hsumsCell := arrayIndexRun sums.val[component.val]!
    iter.start hchannel
  have hsumsMut := arrayIndexMutRun sums component hcomponent
  have hrowUpdate := arrayUpdateRun sums.val[component.val]! iter.start
    (accumulatedChannelValue sums left.val[index.val]! rightComponents
      component iter.start) hchannel
  refine ⟨iter', ?_, startEq, congrArg UScalar.val endEq⟩
  unfold
    V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0.body
  rw [nextRun]
  simp only [hleft, hleftRow, hleftCell, hrightRow, hrightCell,
    hsumsRow, hsumsCell, hsumsMut, bind_tc_ok, Std.lift]
  change
    (do
      let updated ← Array.update sums.val[component.val]! iter.start
        (accumulatedChannelValue sums left.val[index.val]!
          rightComponents component iter.start)
      ok (cont (iter', (sums.set component) updated))) = _
  rw [hrowUpdate]
  rfl

/-- The innermost extracted range loop updates all three channels of exactly
one tower component, with no omitted or duplicated slot. -/
theorem generated_channel_loop_corresponds
    (left : Array RawPrepared 3#usize) (index : Std.Usize)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (component : Std.Usize) (hindex : index.val < 3)
    (hcomponent : component.val < 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (matrixCell base component.val channel).val +
        (cachedChannel left.val[index.val]! component.val channel).val *
        (channelM31 rightComponents component.val channel).val <
          u64Cardinality) :
    V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left base index
          rightComponents component
      ⦃ out => ChannelUpdateInvariant base out left.val[index.val]!
        rightComponents component.val 3 ⦄ := by
  simp only [V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      ChannelUpdateInvariant base state.2 left.val[index.val]!
        rightComponents component.val state.1.start.val)
    (fun out => ChannelUpdateInvariant base out left.val[index.val]!
      rightComponents component.val 3)
  · rintro ⟨iter, current⟩ ⟨hend, hstart, hinvariant⟩
    dsimp only at hend hstart hinvariant ⊢
    by_cases hactive : iter.start.val < iter.end.val
    · obtain ⟨iter', hbody, hnextStart, hnextEnd⟩ :=
        generatedChannelBodyActive left index rightComponents component
          iter current hindex hcomponent hactive hend
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hnextEnd]
        exact hend
      · rw [hnextStart]
        omega
      · rw [hnextStart]
        apply channelUpdateInvariantStep base current left.val[index.val]!
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
      unfold
        V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0.body
      rw [nextRun]
      simpa [hdone] using hinvariant
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro row hrow channel hchannel
    simp

def ComponentUpdateInvariant
    (base current : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val =
      if row < processed then
        (matrixCell base row channel).val +
          (cachedChannel prepared row channel).val *
          (channelM31 rightComponents row channel).val
      else (matrixCell base row channel).val

private theorem componentUpdateInvariantStep
    (base current out : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (component : Std.Usize) (_hcomponent : component.val < 3)
    (houter : ComponentUpdateInvariant base current prepared
      rightComponents component.val)
    (hinner : ChannelUpdateInvariant current out prepared
      rightComponents component.val 3) :
    ComponentUpdateInvariant base out prepared rightComponents
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

private theorem generatedComponentBodyActive
    (left : Array RawPrepared 3#usize) (index : Std.Usize)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hindex : index.val < 3)
    (hactive : iter.start.val < iter.end.val) (hend : iter.end.val = 3)
    (hnoOverflow : ∀ channel, channel < 3 →
      (matrixCell current iter.start.val channel).val +
        (cachedChannel left.val[index.val]! iter.start.val channel).val *
        (channelM31 rightComponents iter.start.val channel).val <
          u64Cardinality) :
    ∃ iter' out,
      V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0.body
          left index rightComponents iter current = ok (cont (iter', out)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      ChannelUpdateInvariant current out left.val[index.val]!
        rightComponents iter.start.val 3 := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter hactive
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have hcomponent : iter.start.val < 3 := by omega
  have innerSpec := generated_channel_loop_corresponds left index
    rightComponents current iter.start hindex hcomponent hnoOverflow
  obtain ⟨out, innerRun, innerPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists innerSpec
  refine ⟨iter', out, ?_, startEq, congrArg UScalar.val endEq, innerPost⟩
  unfold
    V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0.body
  rw [nextRun]
  simp only [bind_tc_ok]
  change
    (do
      let sums1 ←
        V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0_loop0
          { start := 0#usize, «end» := 3#usize } left current index
            rightComponents iter.start
      ok (cont (iter', sums1))) = ok (cont (iter', out))
  rw [innerRun]
  rfl

/-- The middle extracted range loop updates all nine channel cells once for
one prepared/right pair. -/
theorem generated_component_loop_corresponds
    (left : Array RawPrepared 3#usize) (index : Std.Usize)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (base : Array (Array Std.U64 3#usize) 3#usize)
    (hindex : index.val < 3)
    (hnoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell base row channel).val +
        (cachedChannel left.val[index.val]! row channel).val *
        (channelM31 rightComponents row channel).val < u64Cardinality) :
    V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left base index
          rightComponents
      ⦃ out => ComponentUpdateInvariant base out left.val[index.val]!
        rightComponents 3 ⦄ := by
  simp only [V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      ComponentUpdateInvariant base state.2 left.val[index.val]!
        rightComponents state.1.start.val)
    (fun out => ComponentUpdateInvariant base out left.val[index.val]!
      rightComponents 3)
  · rintro ⟨iter, current⟩ ⟨hend, hstart, hinvariant⟩
    dsimp only at hend hstart hinvariant ⊢
    by_cases hactive : iter.start.val < iter.end.val
    · have hcomponent : iter.start.val < 3 := by omega
      have hcurrentNoOverflow : ∀ channel, channel < 3 →
          (matrixCell current iter.start.val channel).val +
            (cachedChannel left.val[index.val]! iter.start.val channel).val *
            (channelM31 rightComponents iter.start.val channel).val <
              u64Cardinality := by
        intro channel hchannel
        have hcurrent := hinvariant iter.start.val hcomponent channel hchannel
        rw [if_neg (by omega)] at hcurrent
        rw [hcurrent]
        exact hnoOverflow iter.start.val hcomponent channel hchannel
      obtain ⟨iter', out, hbody, hnextStart, hnextEnd, hinner⟩ :=
        generatedComponentBodyActive left index rightComponents iter current
          hindex hactive hend hcurrentNoOverflow
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hnextEnd]
        exact hend
      · rw [hnextStart]
        omega
      · rw [hnextStart]
        exact componentUpdateInvariantStep base current out
          left.val[index.val]! rightComponents iter.start hcomponent
          hinvariant hinner
      · rw [hnextStart]
        omega
    · have hdone : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold
        V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0.body
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

theorem generatedComponentMatrixCanonical
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

theorem generatedComponentMatrixExact
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
  have hsumRe := congrArg (fun x : ExactCM31 => x.re) hqsumExact
  have hsumIm := congrArg (fun x : ExactCM31 => x.im) hqsumExact
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

def GeneratedCanonicalQM31Array3 (values : Array RawQM31 3#usize) : Prop :=
  ∀ index, index < 3 → GeneratedCanonicalQM31 values.val[index]!

def PreparedArrayFor3
    (prepared : Array RawPrepared 3#usize)
    (values : Array RawQM31 3#usize) : Prop :=
  ∀ index, index < 3 →
    PreparedFor prepared.val[index]! values.val[index]!

def exactChannelDot
    (left right : Array RawQM31 3#usize) (processed row channel : Nat) :
    ExactM31 :=
  ∑ index ∈ Finset.range processed,
    exactInputChannel (generatedQm31ToExact left.val[index]!) row channel *
      exactInputChannel (generatedQm31ToExact right.val[index]!) row channel

def OuterChannelInvariant
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (left right : Array RawQM31 3#usize) (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val ≤ processed * channelProductBound ∧
    (((matrixCell current row channel).val : Nat) : ExactM31) =
      exactChannelDot left right processed row channel

private theorem channelFactorLe
    (value : RawM31)
    (hvalue : AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val) :
    value.val ≤ m31Modulus - 1 := by
  change value.val < m31Modulus at hvalue
  omega

theorem channelProductLe
    (left right : RawM31)
    (hleft : AspisAeneasCM31Multiplicative.CanonicalRawM31 left.val)
    (hright : AspisAeneasCM31Multiplicative.CanonicalRawM31 right.val) :
    left.val * right.val ≤ channelProductBound := by
  have hl := channelFactorLe left hleft
  have hr := channelFactorLe right hright
  unfold channelProductBound
  simpa [pow_two] using Nat.mul_le_mul hl hr

theorem fourChannelProductsFitU64 :
    4 * channelProductBound < u64Cardinality := by
  norm_num [channelProductBound, m31Modulus, u64Cardinality]

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

private theorem componentPostToSingleProduct
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (prepared : RawPrepared) (left right : RawQM31)
    (rightComponents : Array (Array RawM31 3#usize) 3#usize)
    (hprepared : PreparedFor prepared left)
    (hrightCanonical : CanonicalChannelMatrix rightComponents)
    (hrightExact : ∀ component, component < 3 →
      ∀ channel, channel < 3 →
        (((channelM31 rightComponents component channel).val : Nat) :
          ExactM31) =
          exactInputChannel (generatedQm31ToExact right) component channel)
    (hpost : ComponentUpdateInvariant before after prepared
      rightComponents 3) : SingleProductPost before after left right := by
  intro row hrow channel hchannel
  have hcell := hpost row hrow channel hchannel
  simp only [show row < 3 from hrow, if_pos] at hcell
  have hleftCell := hprepared row hrow channel hchannel
  have hrightCell := hrightCanonical row hrow channel hchannel
  have hproduct := channelProductLe _ _ hleftCell.1 hrightCell
  constructor
  · rw [hcell]
    exact Nat.add_le_add_left hproduct _
  · rw [hcell, Nat.cast_add, Nat.cast_mul, hleftCell.2,
      hrightExact row hrow channel hchannel]

private theorem generatedOuterBodyActive
    (prepared : Array RawPrepared 3#usize)
    (left right : Array RawQM31 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hactive : iter.start.val < iter.end.val) (hend : iter.end.val = 3)
    (hprepared : PreparedArrayFor3 prepared left)
    (hright : GeneratedCanonicalQM31Array3 right)
    (hinvariant : OuterChannelInvariant current left right iter.start.val) :
    ∃ iter' out,
      V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0.body
          prepared right iter current = ok (cont (iter', out)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      SingleProductPost current out left.val[iter.start.val]!
        right.val[iter.start.val]! := by
  have nextSpec := core.iter.range.IteratorRange.next_Usize_some_spec
    iter hactive
  obtain ⟨⟨option, iter'⟩, nextRun, optionEq, startEq, endEq⟩ :=
    Aeneas.Std.WP.spec_imp_exists nextSpec
  rw [optionEq] at nextRun
  have hindex : iter.start.val < 3 := by omega
  let q : RawQM31 := right.val[iter.start.val]!
  have qIndex := arrayIndexRun right iter.start hindex
  have qCanonical : GeneratedCanonicalQM31 q := hright iter.start.val hindex
  obtain ⟨rightSum, rightSumRun, rightSumCanonical, rightSumExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSumSemantics.generated_cm31_add_corresponds
      q.c0 q.c1
      qCanonical.1 qCanonical.2
  obtain ⟨m0, m0Run, m0Canonical, m0Exact⟩ :=
    generated_m31_add_corresponds q.c0.a q.c0.b
      qCanonical.1.1 qCanonical.1.2
  obtain ⟨m1, m1Run, m1Canonical, m1Exact⟩ :=
    generated_m31_add_corresponds q.c1.a q.c1.b
      qCanonical.2.1 qCanonical.2.2
  obtain ⟨m2, m2Run, m2Canonical, m2Exact⟩ :=
    generated_m31_add_corresponds rightSum.a rightSum.b
      rightSumCanonical.1 rightSumCanonical.2
  let rightComponents := generatedComponentMatrix q rightSum m0 m1 m2
  have rightComponentsCanonical : CanonicalChannelMatrix rightComponents :=
    generatedComponentMatrixCanonical q rightSum m0 m1 m2 qCanonical
      rightSumCanonical m0Canonical m1Canonical m2Canonical
  have rightComponentsExact := generatedComponentMatrixExact q rightSum
    m0 m1 m2 rightSumExact m0Exact m1Exact m2Exact
  have currentNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell current row channel).val +
        (cachedChannel prepared.val[iter.start.val]! row channel).val *
        (channelM31 rightComponents row channel).val < u64Cardinality := by
    intro row hrow channel hchannel
    have hbound := (hinvariant row hrow channel hchannel).1
    have hleftCell := hprepared iter.start.val hindex row hrow channel hchannel
    have hrightCell := rightComponentsCanonical row hrow channel hchannel
    have hproduct := channelProductLe _ _ hleftCell.1 hrightCell
    have hcount : iter.start.val + 1 ≤ 4 := by omega
    calc
      (matrixCell current row channel).val +
          (cachedChannel prepared.val[iter.start.val]! row channel).val *
            (channelM31 rightComponents row channel).val
          ≤ iter.start.val * channelProductBound + channelProductBound :=
            Nat.add_le_add hbound hproduct
      _ = (iter.start.val + 1) * channelProductBound := by ring
      _ ≤ 4 * channelProductBound :=
        Nat.mul_le_mul_right channelProductBound hcount
      _ < u64Cardinality := fourChannelProductsFitU64
  have componentSpec := generated_component_loop_corresponds prepared
    iter.start rightComponents current hindex currentNoOverflow
  obtain ⟨out, componentRun, componentPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists componentSpec
  have singlePost := componentPostToSingleProduct current out
    prepared.val[iter.start.val]! left.val[iter.start.val]! q
    rightComponents (hprepared iter.start.val hindex)
    rightComponentsCanonical rightComponentsExact componentPost
  refine ⟨iter', out, ?_, startEq, congrArg UScalar.val endEq, ?_⟩
  · unfold
      V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0.body
    rw [nextRun]
    simp only [bind_tc_ok]
    rw [qIndex]
    simp only [bind_tc_ok]
    change
      (do
        let rightSum1 ←
          V7CallerCurrentReleaseR26.field.CM31.add q.c0 q.c1
        let m01 ←
          V7CallerCurrentReleaseR26.field.M31.add q.c0.a q.c0.b
        let m11 ←
          V7CallerCurrentReleaseR26.field.M31.add q.c1.a q.c1.b
        let m21 ←
          V7CallerCurrentReleaseR26.field.M31.add
            rightSum1.a rightSum1.b
        let sums1 ←
          V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0_loop0
            { start := 0#usize, «end» := 3#usize } prepared current
              iter.start
              (generatedComponentMatrix q rightSum1 m01 m11 m21)
        ok (cont (iter', sums1))) = ok (cont (iter', out))
    rw [rightSumRun]
    simp only [bind_tc_ok]
    rw [m0Run]
    simp only [bind_tc_ok]
    rw [m1Run]
    simp only [bind_tc_ok]
    rw [m2Run]
    simp only [bind_tc_ok]
    rw [componentRun]
    rfl
  · simpa [q] using singlePost

private theorem outerInvariantStep
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : Array RawQM31 3#usize) (processed : Nat)
    (hinvariant : OuterChannelInvariant before left right processed)
    (hpost : SingleProductPost before after left.val[processed]!
      right.val[processed]!) :
    OuterChannelInvariant after left right (processed + 1) := by
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
    simp [exactChannelDot, Finset.sum_range_succ]

/-- The complete extracted outer loop accumulates exactly the two prepared
products, in array order, with a proved no-overflow bound. -/
theorem generated_outer_loop_corresponds
    (prepared : Array RawPrepared 3#usize)
    (left right : Array RawQM31 3#usize)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (hprepared : PreparedArrayFor3 prepared left)
    (hright : GeneratedCanonicalQM31Array3 right)
    (hinitial : OuterChannelInvariant initial left right 0) :
    V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0
        { start := 0#usize, «end» := 3#usize } prepared right initial
      ⦃ out => OuterChannelInvariant out left right 3 ⦄ := by
  simp only [V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      OuterChannelInvariant state.2 left right state.1.start.val)
    (fun out => OuterChannelInvariant out left right 3)
  · rintro ⟨iter, current⟩ ⟨hend, hstart, hinvariant⟩
    dsimp only at hend hstart hinvariant ⊢
    by_cases hactive : iter.start.val < iter.end.val
    · obtain ⟨iter', out, hbody, hnextStart, hnextEnd, hpost⟩ :=
        generatedOuterBodyActive prepared left right iter current hactive
          hend hprepared hright hinvariant
      rw [hbody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hnextEnd]
        exact hend
      · rw [hnextStart]
        omega
      · rw [hnextStart]
        exact outerInvariantStep current out left right iter.start.val
          hinvariant hpost
      · rw [hnextStart]
        omega
    · have hdone : iter.start.val = 3 := by omega
      have nextSpec := core.iter.range.IteratorRange.next_Usize_none_spec
        iter (by omega)
      obtain ⟨⟨option, iter'⟩, nextRun, optionEq, iterEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists nextSpec
      rw [optionEq, iterEq] at nextRun
      unfold
        V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared_loop0.body
      rw [nextRun]
      simpa [hdone] using hinvariant
  · exact ⟨by norm_num, by norm_num, hinitial⟩

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

theorem zero_outer_invariant
    (left right : Array RawQM31 3#usize) :
    OuterChannelInvariant zeroU64ChannelMatrix left right 0 := by
  intro row hrow channel hchannel
  rw [zeroMatrixCell row channel hrow hchannel]
  simp [exactChannelDot]

def reconstructCMExact (row : Array Std.U64 3#usize) : ExactCM31 :=
  ⟨((rowCell row 0).val : ExactM31) -
      ((rowCell row 1).val : ExactM31),
    ((rowCell row 2).val : ExactM31) -
      ((rowCell row 0).val : ExactM31) -
      ((rowCell row 1).val : ExactM31)⟩

def reconstructQMExact
    (sums : Array (Array Std.U64 3#usize) 3#usize) : ExactQM31 :=
  let m0 := reconstructCMExact sums.val[0]!
  let m1 := reconstructCMExact sums.val[1]!
  let m2 := reconstructCMExact sums.val[2]!
  ⟨m0 + exactQm31R * m1,
    m2 - m0 - m1⟩

theorem generated_cm31_sub_corresponds
    (x y : RawCM31) (hx : GeneratedCanonicalCM31 x) (hy : GeneratedCanonicalCM31 y) :
    ∃ out : RawCM31,
      V7CallerCurrentReleaseR26.field.CM31.sub x y = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = generatedCm31ToExact x - generatedCm31ToExact y := by
  obtain ⟨oa, ha, hca, ea⟩ := generated_m31_sub_corresponds
    x.a y.a hx.1 hy.1
  obtain ⟨ob, hb, hcb, eb⟩ := generated_m31_sub_corresponds
    x.b y.b hx.2 hy.2
  refine ⟨⟨oa, ob⟩, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp [V7CallerCurrentReleaseR26.field.CM31.sub, ha, hb]
  · apply QuadraticAlgebra.ext
    · exact ea
    · exact eb

theorem generated_mul_by_r_corresponds
    (x : RawCM31) (hx : GeneratedCanonicalCM31 x) :
    ∃ out : RawCM31,
      V7CallerCurrentReleaseR26.field.mul_by_r x = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out =
        exactQm31R * generatedCm31ToExact x := by
  obtain ⟨out, run, canonical, exact⟩ :=
    V7CallerCurrentReleaseR26FieldBridge.generated_mul_by_r_corresponds x hx
  refine ⟨out, run, canonical, ?_⟩
  simpa [mul_comm] using exact

private theorem generatedReconstructClosureCorresponds
    (channels : Array Std.U64 3#usize) :
    ∃ out : RawCM31,
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () channels = ok out ∧
      GeneratedCanonicalCM31 out ∧
      generatedCm31ToExact out = reconstructCMExact channels := by
  have h0 := arrayIndexRun channels 0#usize (by norm_num)
  have h1 := arrayIndexRun channels 1#usize (by norm_num)
  have h2 := arrayIndexRun channels 2#usize (by norm_num)
  obtain ⟨m0, m0Run, m0Canonical, m0Exact⟩ :=
    generated_m31_reduce_u64_corresponds (rowCell channels 0)
  obtain ⟨m1, m1Run, m1Canonical, m1Exact⟩ :=
    generated_m31_reduce_u64_corresponds (rowCell channels 1)
  obtain ⟨m2, m2Run, m2Canonical, m2Exact⟩ :=
    generated_m31_reduce_u64_corresponds (rowCell channels 2)
  obtain ⟨real, realRun, realCanonical, realExact⟩ :=
    generated_m31_sub_corresponds m0 m1 m0Canonical m1Canonical
  obtain ⟨imag0, imag0Run, imag0Canonical, imag0Exact⟩ :=
    generated_m31_sub_corresponds m2 m0 m2Canonical m0Canonical
  obtain ⟨imag, imagRun, imagCanonical, imagExact⟩ :=
    generated_m31_sub_corresponds imag0 m1 imag0Canonical m1Canonical
  have m0Run' :
      V7CallerCurrentReleaseR26.field.M31.reduce_u64
          channels.val[(0#usize).val]! = ok m0 := by
    simpa [rowCell] using m0Run
  have m1Run' :
      V7CallerCurrentReleaseR26.field.M31.reduce_u64
          channels.val[(1#usize).val]! = ok m1 := by
    simpa [rowCell] using m1Run
  have m2Run' :
      V7CallerCurrentReleaseR26.field.M31.reduce_u64
          channels.val[(2#usize).val]! = ok m2 := by
    simpa [rowCell] using m2Run
  refine ⟨⟨real, imag⟩, ?_, ⟨realCanonical, imagCanonical⟩, ?_⟩
  · unfold
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
    rw [h0]
    simp only [bind_tc_ok]
    rw [m0Run', h1]
    simp only [bind_tc_ok]
    rw [m1Run', h2]
    simp only [bind_tc_ok]
    rw [m2Run']
    simp only [bind_tc_ok]
    rw [realRun]
    simp only [bind_tc_ok]
    rw [imag0Run]
    simp only [bind_tc_ok]
    rw [imagRun]
    rfl
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) = _
      simp only [generatedM31ToExact] at m0Exact m1Exact
      rw [realExact, m0Exact, m1Exact]
      rfl
    · change ((imag.val : Nat) : ExactM31) = _
      simp only [generatedM31ToExact] at m0Exact m1Exact m2Exact
      rw [imagExact, imag0Exact, m0Exact, m1Exact, m2Exact]
      rfl

/-- Exact reconstruction of the nine delayed-reduction channels in the fresh
linked extraction. -/
theorem generated_reconstruction_corresponds
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    ∃ out : RawQM31,
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums
          sums = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = reconstructQMExact sums := by
  have hrow0 := arrayIndexRun sums 0#usize (by norm_num)
  have hrow1 := arrayIndexRun sums 1#usize (by norm_num)
  have hrow2 := arrayIndexRun sums 2#usize (by norm_num)
  obtain ⟨m0, m0Run, m0Canonical, m0Exact⟩ :=
    generatedReconstructClosureCorresponds sums.val[0]!
  obtain ⟨m1, m1Run, m1Canonical, m1Exact⟩ :=
    generatedReconstructClosureCorresponds sums.val[1]!
  obtain ⟨m2, m2Run, m2Canonical, m2Exact⟩ :=
    generatedReconstructClosureCorresponds sums.val[2]!
  obtain ⟨rm1, rm1Run, rm1Canonical, rm1Exact⟩ :=
    generated_mul_by_r_corresponds m1 m1Canonical
  obtain ⟨low, lowRun, lowCanonical, lowExact⟩ :=
    V7CallerCurrentReleaseR26PreparedSumSemantics.generated_cm31_add_corresponds
      m0 rm1 m0Canonical rm1Canonical
  obtain ⟨high0, high0Run, high0Canonical, high0Exact⟩ :=
    generated_cm31_sub_corresponds m2 m0 m2Canonical m0Canonical
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_cm31_sub_corresponds high0 m1 high0Canonical m1Canonical
  have m0Run' :
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () sums.val[(0#usize).val]! = ok m0 := by
    simpa using m0Run
  have m1Run' :
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () sums.val[(1#usize).val]! = ok m1 := by
    simpa using m1Run
  have m2Run' :
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () sums.val[(2#usize).val]! = ok m2 := by
    simpa using m2Run
  refine ⟨⟨low, high⟩, ?_, ⟨lowCanonical, highCanonical⟩, ?_⟩
  · unfold
      V7CallerCurrentReleaseR26.field.qm31_from_karatsuba_channel_sums
    rw [hrow0]
    simp only [bind_tc_ok]
    rw [m0Run', hrow1]
    simp only [bind_tc_ok]
    rw [m1Run', hrow2]
    simp only [bind_tc_ok]
    rw [m2Run']
    simp only [bind_tc_ok]
    rw [rm1Run]
    simp only [bind_tc_ok]
    rw [lowRun, high0Run]
    simp only [bind_tc_ok]
    rw [highRun]
    rfl
  · apply QuadraticAlgebra.ext
    · change generatedCm31ToExact low = _
      rw [lowExact, rm1Exact, m0Exact, m1Exact]
      rfl
    · change generatedCm31ToExact high = _
      rw [highExact, high0Exact, m0Exact, m1Exact, m2Exact]
      rfl

def exactProductDot3
    (left right : Array RawQM31 3#usize) : ExactQM31 :=
  ∑ index ∈ Finset.range 3,
    generatedQm31ToExact left.val[index]! *
      generatedQm31ToExact right.val[index]!

private theorem reconstructExactEqProductDot
    (left right : Array RawQM31 3#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hinvariant : OuterChannelInvariant sums left right 3) :
    reconstructQMExact sums = exactProductDot3 left right := by
  have h00 := (hinvariant 0 (by omega) 0 (by omega)).2
  have h01 := (hinvariant 0 (by omega) 1 (by omega)).2
  have h02 := (hinvariant 0 (by omega) 2 (by omega)).2
  have h10 := (hinvariant 1 (by omega) 0 (by omega)).2
  have h11 := (hinvariant 1 (by omega) 1 (by omega)).2
  have h12 := (hinvariant 1 (by omega) 2 (by omega)).2
  have h20 := (hinvariant 2 (by omega) 0 (by omega)).2
  have h21 := (hinvariant 2 (by omega) 1 (by omega)).2
  have h22 := (hinvariant 2 (by omega) 2 (by omega)).2
  unfold matrixCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot3,
        exactChannelDot, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h10, h11, h12]
      ring
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot3,
        exactChannelDot, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h02, h10, h11, h12]
      ring
  · apply QuadraticAlgebra.ext
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot3,
        exactChannelDot, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h10, h11, h20, h21]
      ring
    · simp [reconstructQMExact, reconstructCMExact, exactProductDot3,
        exactChannelDot, exactInputChannel, exactQMComponent,
        exactCMChannel, exactQm31R,
        Finset.sum_range_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢
      rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
      ring

def addConstantChannels
    (constant : RawQM31)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    Array (Array Std.U64 3#usize) 3#usize :=
  let a0 : Std.U64 := UScalar.cast .U64 constant.c0.a
  let b0 : Std.U64 := UScalar.cast .U64 constant.c0.b
  let a1 : Std.U64 := UScalar.cast .U64 constant.c1.a
  let b1 : Std.U64 := UScalar.cast .U64 constant.c1.b
  let sums2 := sums.set 0#usize
    ((sums.val[0]!).set 0#usize
      (Std.U64.wrapping_add (sums.val[0]!.val[0]!) a0))
  let sums3 := sums2.set 0#usize
    ((sums2.val[0]!).set 2#usize
      (Std.U64.wrapping_add (sums2.val[0]!.val[2]!)
        (Std.U64.wrapping_add a0 b0)))
  let sums4 := sums3.set 2#usize
    ((sums3.val[2]!).set 0#usize
      (Std.U64.wrapping_add (sums3.val[2]!.val[0]!)
        (Std.U64.wrapping_add a0 a1)))
  sums4.set 2#usize
    ((sums4.val[2]!).set 2#usize
      (Std.U64.wrapping_add (sums4.val[2]!.val[2]!)
        (Std.U64.wrapping_add
          (Std.U64.wrapping_add (Std.U64.wrapping_add a0 a1) b0) b1)))

private theorem u64WrappingAddNoWrap
    (x y : Std.U64) (h : x.val + y.val < u64Cardinality) :
    (Std.U64.wrapping_add x y).val = x.val + y.val := by
  rw [Std.U64.wrapping_add_val_eq]
  have hsize : UScalar.size .U64 = u64Cardinality := by
    simpa [u64Cardinality, AspisAeneasM31ReduceU64.u64Cardinality] using
      AspisAeneasM31ReduceU64.u64_size_eq
  rw [hsize, Nat.mod_eq_of_lt h]

private theorem reconstructAddConstant
    (constant : RawQM31)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hbound : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell sums row channel).val ≤ 3 * channelProductBound) :
    reconstructQMExact (addConstantChannels constant sums) =
      generatedQm31ToExact constant + reconstructQMExact sums := by
  have h00 := hbound 0 (by omega) 0 (by omega)
  have h02 := hbound 0 (by omega) 2 (by omega)
  have h20 := hbound 2 (by omega) 0 (by omega)
  have h22 := hbound 2 (by omega) 2 (by omega)
  have ha0 := UScalar.hBounds constant.c0.a
  have hb0 := UScalar.hBounds constant.c0.b
  have ha1 := UScalar.hBounds constant.c1.a
  have hb1 := UScalar.hBounds constant.c1.b
  simp only [UScalarTy.U32_numBits_eq] at ha0 hb0 ha1 hb1
  have hab : constant.c0.a.val + constant.c0.b.val < u64Cardinality := by
    norm_num [u64Cardinality] at ha0 hb0 ⊢
    omega
  have haa : constant.c0.a.val + constant.c1.a.val < u64Cardinality := by
    norm_num [u64Cardinality] at ha0 ha1 ⊢
    omega
  have haab : constant.c0.a.val + constant.c1.a.val +
      constant.c0.b.val < u64Cardinality := by
    norm_num [u64Cardinality] at ha0 hb0 ha1 ⊢
    omega
  have haabb : constant.c0.a.val + constant.c1.a.val +
      constant.c0.b.val + constant.c1.b.val < u64Cardinality := by
    norm_num [u64Cardinality] at ha0 hb0 ha1 hb1 ⊢
    omega
  have hcell00 : (matrixCell sums 0 0).val + constant.c0.a.val <
      u64Cardinality := by
    norm_num [channelProductBound, m31Modulus, u64Cardinality] at h00 ha0 ⊢
    omega
  have hcell02 : (matrixCell sums 0 2).val +
      (constant.c0.a.val + constant.c0.b.val) < u64Cardinality := by
    norm_num [channelProductBound, m31Modulus, u64Cardinality] at h02 ha0 hb0 ⊢
    omega
  have hcell20 : (matrixCell sums 2 0).val +
      (constant.c0.a.val + constant.c1.a.val) < u64Cardinality := by
    norm_num [channelProductBound, m31Modulus, u64Cardinality] at h20 ha0 ha1 ⊢
    omega
  have hcell22 : (matrixCell sums 2 2).val +
      (constant.c0.a.val + constant.c1.a.val + constant.c0.b.val +
        constant.c1.b.val) < u64Cardinality := by
    norm_num [channelProductBound, m31Modulus, u64Cardinality] at h22 ha0 hb0 ha1 hb1 ⊢
    omega
  unfold matrixCell rowCell at hcell00 hcell02 hcell20 hcell22
  have hsize : UScalar.size .U64 = u64Cardinality := by
    simpa [u64Cardinality, AspisAeneasM31ReduceU64.u64Cardinality] using
      AspisAeneasM31ReduceU64.u64_size_eq
  have hmod00 :
      ((sums.val[0]!.val[0]!).val + constant.c0.a.val) %
          UScalar.size .U64 =
        (sums.val[0]!.val[0]!).val + constant.c0.a.val := by
    rw [hsize, Nat.mod_eq_of_lt hcell00]
  have hmod00' :
      (constant.c0.a.val + (sums.val[0]!.val[0]!).val) %
          UScalar.size .U64 =
        constant.c0.a.val + (sums.val[0]!.val[0]!).val := by
    rw [Nat.add_comm, hmod00]
  have hmod02 :
      ((sums.val[0]!.val[2]!).val + constant.c0.a.val +
          constant.c0.b.val) % UScalar.size .U64 =
        (sums.val[0]!.val[2]!).val + constant.c0.a.val +
          constant.c0.b.val := by
    rw [hsize, Nat.mod_eq_of_lt (by omega)]
  have hmod20 :
      (constant.c0.a.val + constant.c1.a.val +
          (sums.val[2]!.val[0]!).val) % UScalar.size .U64 =
        constant.c0.a.val + constant.c1.a.val +
          (sums.val[2]!.val[0]!).val := by
    rw [hsize, Nat.mod_eq_of_lt (by omega)]
  have hmod22 :
      ((sums.val[2]!.val[2]!).val + constant.c0.a.val +
          constant.c1.a.val + constant.c0.b.val + constant.c1.b.val) %
          UScalar.size .U64 =
        (sums.val[2]!.val[2]!).val + constant.c0.a.val +
          constant.c1.a.val + constant.c0.b.val + constant.c1.b.val := by
    rw [hsize, Nat.mod_eq_of_lt (by omega)]
  norm_num at hmod00 hmod00' hmod02 hmod20 hmod22
  norm_num at hcell00 hcell02 hcell20 hcell22
  have hmod02' :
      (constant.c0.a.val + constant.c0.b.val +
          (sums.val[0].val[2]).val) % UScalar.size .U64 =
        constant.c0.a.val + constant.c0.b.val +
          (sums.val[0].val[2]).val := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmod02
  have hmod20' :
      ((sums.val[2].val[0]).val + constant.c0.a.val +
          constant.c1.a.val) % UScalar.size .U64 =
        (sums.val[2].val[0]).val + constant.c0.a.val +
          constant.c1.a.val := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmod20
  have hmod02r :
      ((sums.val[0].val[2]).val +
          (constant.c0.a.val + constant.c0.b.val)) % Std.U64.size =
        (sums.val[0].val[2]).val +
          (constant.c0.a.val + constant.c0.b.val) := by
    rw [show Std.U64.size = u64Cardinality by
      norm_num [u64Cardinality, Std.U64.size, Std.U64.numBits,
        UScalarTy.U64_numBits_eq]]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod20r :
      ((sums.val[2].val[0]).val +
          (constant.c0.a.val + constant.c1.a.val)) % Std.U64.size =
        (sums.val[2].val[0]).val +
          (constant.c0.a.val + constant.c1.a.val) := by
    rw [show Std.U64.size = u64Cardinality by
      norm_num [u64Cardinality, Std.U64.size, Std.U64.numBits,
        UScalarTy.U64_numBits_eq]]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod22r :
      ((sums.val[2].val[2]).val +
          (constant.c0.a.val + constant.c1.a.val + constant.c0.b.val +
            constant.c1.b.val)) % Std.U64.size =
        (sums.val[2].val[2]).val +
          (constant.c0.a.val + constant.c1.a.val + constant.c0.b.val +
            constant.c1.b.val) := by
    rw [show Std.U64.size = u64Cardinality by
      norm_num [u64Cardinality, Std.U64.size, Std.U64.numBits,
        UScalarTy.U64_numBits_eq]]
    exact Nat.mod_eq_of_lt (by omega)
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext
  all_goals simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  all_goals
    simp [reconstructQMExact, reconstructCMExact, addConstantChannels,
      rowCell, Array.set_val_eq, UScalarTy.U64_numBits_eq,
      hmod00,
      generatedQm31ToExact, generatedCm31ToExact, exactQm31R]
  case re.re => ring
  case re.im =>
    rw [hmod02r]
    simp only [Nat.cast_add]
    ring
  case im.re =>
    rw [hmod20r]
    simp only [Nat.cast_add]
    ring
  case im.im =>
    rw [hmod22r, hmod20r, hmod02r]
    simp only [Nat.cast_add]
    ring

/-- The current extracted fused helper returns the constant plus the exact
three-product dot represented by its prepared left inputs. -/
theorem generated_add_sum_products3_prepared_corresponds
    (constant : RawQM31)
    (prepared : Array RawPrepared 3#usize)
    (left right : Array RawQM31 3#usize)
    (hprepared : PreparedArrayFor3 prepared left)
    (hright : GeneratedCanonicalQM31Array3 right) :
    ∃ out : RawQM31,
      V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared
          constant prepared right = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out =
        generatedQm31ToExact constant + exactProductDot3 left right := by
  have loopSpec := generated_outer_loop_corresponds prepared left right
    zeroU64ChannelMatrix hprepared hright (zero_outer_invariant left right)
  obtain ⟨sums, loopRun, sumsInvariant⟩ :=
    Aeneas.Std.WP.spec_imp_exists loopSpec
  obtain ⟨out, reconstructRun, canonical, reconstructExact⟩ :=
    generated_reconstruction_corresponds (addConstantChannels constant sums)
  refine ⟨out, ?_, canonical, ?_⟩
  · unfold V7CallerCurrentReleaseR26.field.qm31_add_sum_products3_prepared
    unfold zeroU64ChannelMatrix at loopRun
    simp only at loopRun ⊢
    rw [loopRun]
    simp only [bind_tc_ok]
    rw [← reconstructRun]
    simp [from_u64_u32_eq_cast, addConstantChannels, Array.index_usize,
      Array.index_mut_usize, Array.update, Std.lift]
    congr 1
  · rw [reconstructExact]
    rw [reconstructAddConstant constant sums (fun row hrow channel hchannel =>
      (sumsInvariant row hrow channel hchannel).1)]
    rw [reconstructExactEqProductDot left right sums sumsInvariant]

#print axioms generated_outer_loop_corresponds
#print axioms reconstructAddConstant
#print axioms generated_add_sum_products3_prepared_corresponds

end V7CallerCurrentReleaseR26PreparedSum3Semantics
