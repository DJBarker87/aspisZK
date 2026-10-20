import S3ActualGroupedPairPrefixFormulaV1
import S3S9CurrentSourceModel
import AspisR1GroupedPairCut.Proofs.S3GroupedPairGroupTableBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairSourceRow

open AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairPrefixFormula
open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1OuterPrefixPublic
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop1
open AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition
open AspisR1.S3S9CurrentSourceModel

abbrev Wide := AspisWideTower.WideExact

private def prefixFiniteSum (mask : Nat) (xs : List Wide) (n : Nat) : Wide :=
  ∑ i : Fin n, if bitAt mask i.val = 1 then xs.getD i.val 0 else 0

private theorem actualSelectedPrefix_eq_prefixFiniteSum
    (mask : Nat) (xs : List Wide) :
    ∀ n, actualSelectedPrefix mask n xs = prefixFiniteSum mask xs n := by
  intro n
  induction n with
  | zero => simp [actualSelectedPrefix, prefixFiniteSum]
  | succ n ih =>
      rw [actualSelectedPrefix, ih]
      change (∑ i : Fin n, if bitAt mask i.val = 1 then xs.getD i.val 0 else 0) +
          (if bitAt mask n = 1 then (xs.drop n).headD 0 else 0) =
        ∑ i : Fin (n + 1), if bitAt mask i.val = 1 then xs.getD i.val 0 else 0
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [List.headD_eq_getD, List.getD_eq_getElem?_getD,
        List.getElem?_drop, Nat.add_zero, ← List.getD_eq_getElem?_getD]

private def prefixCoefficientSum (input : Nat → Wide) (n : Nat) (g : Fin 12) : Wide :=
  ∑ j : Fin n,
    if inactiveGroups[j.val]?.getD 0 = g.val then input j.val else 0

private theorem actual_group_values_eq_source :
    weights.S2_INACTIVE_GROUPS.val.map (fun x => x.val) = inactiveGroups := by
  simp only [weights.S2_INACTIVE_GROUPS, inactiveGroups, Array.make]
  rfl

private theorem list_getD_map_u8 (xs : List Std.U8) (i : Nat)
    (hi : i < xs.length) :
    (xs.map (fun x => x.val)).getD i 0 = (xs.getD i 0#u8).val := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simp at hi; omega)

private theorem modelGroup_value_eq_source (n : Nat) (hn : n < 64) :
    (modelGroup n).val = inactiveGroups.getD n 0 := by
  unfold modelGroup
  rw [dif_pos hn]
  have htable := congrArg (fun xs : List Nat => xs.getD n 0)
    actual_group_values_eq_source
  have hread : actualGroupVal ⟨n, hn⟩ =
      (weights.S2_INACTIVE_GROUPS.val.map (fun x => x.val)).getD n 0 := by
    have hnArray : n < weights.S2_INACTIVE_GROUPS.val.length := by
      have hp := weights.S2_INACTIVE_GROUPS.property
      change weights.S2_INACTIVE_GROUPS.val.length = 64 at hp
      omega
    change (weights.S2_INACTIVE_GROUPS.val[n]'hnArray).val = _
    rw [← List.getD_eq_getElem _ _ hnArray]
    exact (list_getD_map_u8 weights.S2_INACTIVE_GROUPS.val n hnArray).symm
  exact hread.trans htable

private theorem prefixMeaning_eq_prefixCoefficientSum
    (input : Nat → Wide) :
    ∀ n, n ≤ 64 → ∀ g : Fin 12,
      PrefixMeaning input (fun _ => 0) n g = prefixCoefficientSum input n g := by
  intro n
  induction n with
  | zero =>
      intro _ g
      simp [PrefixMeaning, prefixCoefficientSum]
  | succ n ih =>
      intro hn g
      have hnlt : n < 64 := by omega
      have hmodel := modelGroup_value_eq_source n hnlt
      have ihg := ih (by omega) g
      have ihm := ih (by omega) (modelGroup n)
      rw [PrefixMeaning]
      change (if g.val = (modelGroup n).val then
        PrefixMeaning input (fun _ => 0) n (modelGroup n) + input n
        else PrefixMeaning input (fun _ => 0) n g) = _
      rw [ihg, ihm]
      unfold prefixCoefficientSum
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hmodel' : (modelGroup n).val = inactiveGroups[n]?.getD 0 := by
        simpa only [List.getD_eq_getElem?_getD] using hmodel
      rw [hmodel']
      by_cases hg : g.val = inactiveGroups[n]?.getD 0
      · have hg' : inactiveGroups[n]?.getD 0 = g.val := hg.symm
        rw [hg']
        simp only [if_true]
      · have hg' : inactiveGroups[n]?.getD 0 ≠ g.val := fun h => hg h.symm
        simp only [if_neg hg, if_neg hg']
        simp only [add_zero]

private def actualLowValue (low : List Wide) (s : Fin 16) : Wide :=
  low.getD s.val 0

private def sourceGroupWeight (low : List Wide) (g : Fin 12) : Wide :=
  ∑ s : Fin 16, if inactiveAtGroup g s then actualLowValue low s else 0

private theorem actual_mask_values_eq_model :
    weights.S2_INACTIVE_MASKS.val.map (fun x => x.val) = inactiveMasks := by
  simp only [weights.S2_INACTIVE_MASKS, inactiveMasks, Array.make]
  rfl

private theorem list_getD_map_u16 (xs : List Std.U16) (i : Nat)
    (hi : i < xs.length) :
    (xs.map (fun x => x.val)).getD i 0 = (xs.getD i 0#u16).val := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simp at hi; omega)

private theorem actualMaskValue_eq_model (g : Fin 12) :
    (weights.S2_INACTIVE_MASKS.val[g.val]'(by
      have hp := weights.S2_INACTIVE_MASKS.property
      change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
      omega)).val = inactiveMasks.getD g.val 0 := by
  have htable := congrArg (fun xs : List Nat => xs.getD g.val 0)
    actual_mask_values_eq_model
  have hread : (weights.S2_INACTIVE_MASKS.val[g.val]'(by
      have hp := weights.S2_INACTIVE_MASKS.property
      change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
      omega)).val =
      (weights.S2_INACTIVE_MASKS.val.map (fun x => x.val)).getD g.val 0 := by
    have hglen : g.val < weights.S2_INACTIVE_MASKS.val.length := by
      have hp := weights.S2_INACTIVE_MASKS.property
      change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
      omega
    change (weights.S2_INACTIVE_MASKS.val[g.val]'hglen).val = _
    rw [← List.getD_eq_getElem _ _ hglen]
    exact (list_getD_map_u16 weights.S2_INACTIVE_MASKS.val g.val hglen).symm
  exact hread.trans htable

private theorem actualSelectedPrefix_eq_sourceGroupWeight
    (low : Array field.WideExact 16#usize) (g : Fin 12) :
    actualSelectedPrefix
        (weights.S2_INACTIVE_MASKS.val[g.val]'(by
          have hp := weights.S2_INACTIVE_MASKS.property
          change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
          omega)).val 16 (low.val.map decode) = sourceGroupWeight (low.val.map decode) g := by
  rw [actualSelectedPrefix_eq_prefixFiniteSum]
  unfold prefixFiniteSum sourceGroupWeight actualLowValue
  apply Finset.sum_congr rfl
  intro s _
  rw [actualMaskValue_eq_model]
  simp [inactiveAtGroup, bitAt]

/-- The parser recurrence for 64 actual loop-0 rows identifies each grouped
coefficient with the corresponding source group sum. -/
theorem prefixMeaning_eq_sourceCoefficientSum (input : Nat → Wide) (g : Fin 12) :
    PrefixMeaning input (fun _ => 0) 64 g =
      ∑ j : Fin 64, if groupAt j = g then input j.val else 0 := by
  rw [prefixMeaning_eq_prefixCoefficientSum input 64 le_rfl g]
  apply Finset.sum_congr rfl
  intro j _
  have hgroup : groupAt j = g ↔ inactiveGroups[j.val]?.getD 0 = g.val := by
    constructor
    · intro h
      simpa only [groupAt, Fin.val_mk, List.getD_eq_getElem?_getD] using
        congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [groupAt, Fin.val_mk, List.getD_eq_getElem?_getD] using h
  simp [hgroup]

/-- The same 12-step outer recurrence is the source model's grouped-pair
functional, with its coefficients supplied by the actual parser-backed
loop-0 recurrence and its weights supplied by the actual 16-step mask loop. -/
private theorem parser_group_contribution_eq_source_term
    (low : Array field.WideExact 16#usize) (input : Nat → Wide)
    (g : Fin 12) :
    parserGroupContribution low input g.val =
      (∑ j : Fin 64, if groupAt j = g then input j.val else 0) *
        sourceGroupWeight (low.val.map decode) g := by
  have hcontribution : parserGroupContribution low input g.val =
      PrefixMeaning input (fun _ => 0) 64 g *
        actualSelectedPrefix
          (weights.S2_INACTIVE_MASKS.val[g.val]'(by
            have hp := weights.S2_INACTIVE_MASKS.property
            change weights.S2_INACTIVE_MASKS.val.length = 12 at hp
            omega)).val 16 (low.val.map decode) := by
    unfold parserGroupContribution
    simp only [dif_pos g.isLt]
  have hcoeff := prefixMeaning_eq_sourceCoefficientSum input g
  have hweight := actualSelectedPrefix_eq_sourceGroupWeight low g
  exact hcontribution.trans (congrArg₂ (fun a b : Wide => a * b) hcoeff hweight)

private theorem parser_grouped_prefix_eq_contributions
    (low : Array field.WideExact 16#usize) (input : Nat → Wide) :
    ∀ n : Nat, n ≤ 12 →
      parserGroupedPrefix low input n =
        ∑ g : Fin n, parserGroupContribution low input g.val := by
  intro n
  induction n with
  | zero => intro _; simp [parserGroupedPrefix]
  | succ n ih =>
      intro hn
      rw [parserGroupedPrefix, ih (by omega), Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]

theorem parserGroupedPrefix_eq_source_groupedPair
    (low : Array field.WideExact 16#usize) (input : Nat → Wide) :
    parserGroupedPrefix low input 12 =
      groupedPair (fun j => input j.val) (actualLowValue (low.val.map decode))
        groupAt inactiveAtGroup := by
  rw [parser_grouped_prefix_eq_contributions low input 12 le_rfl]
  conv_rhs => unfold groupedPair
  apply Finset.sum_congr rfl
  intro g _
  rw [parser_group_contribution_eq_source_term low input g]
  simp only [sourceGroupWeight]

/-- Actual source execution now lands on the concrete classified-row
functional. The remaining low-input canonicality condition is exactly the
caller's parser/canonical-input boundary retained by the helper proof. -/
theorem actual_grouped_success_has_source_row_functional
    (bytes : Slice Std.U8) (low : Array field.WideExact 16#usize)
    (out : field.WideExact) (hlow : CanonicalLow low)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out) :
    ∃ coefficients,
      weights.s2_grouped_inactive_pair_loop0 actualOperations
        { start := 0#usize, «end» := 64#usize } bytes
        (Array.repeat 12#usize field.WideExact.ZERO) = .ok coefficients ∧
      DecodedMeaning coefficients
        (PrefixMeaning (successfulInput bytes low out h) (fun _ => 0) 64) ∧
      decode out =
        ungroupedPair (fun j => successfulInput bytes low out h j.val)
          (actualLowValue (low.val.map decode)) inactiveAtSource := by
  obtain ⟨coefficients, hloop0, hprefix, hrow⟩ :=
    actual_grouped_success_has_parser_grouped_value bytes low out hlow h
  refine ⟨coefficients, hloop0, hprefix, ?_⟩
  rw [hrow, parserGroupedPrefix_eq_source_groupedPair]
  exact s3_grouped_pair_exact
    (fun j => successfulInput bytes low out h j.val)
    (actualLowValue (low.val.map decode))

#print axioms actualSelectedPrefix_eq_prefixFiniteSum
#print axioms prefixMeaning_eq_sourceCoefficientSum
#print axioms parserGroupedPrefix_eq_source_groupedPair
#print axioms actual_grouped_success_has_source_row_functional

end AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairSourceRow
