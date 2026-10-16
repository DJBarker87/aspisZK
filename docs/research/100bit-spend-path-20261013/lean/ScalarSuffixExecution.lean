import ScalarSuffixSlice
import ScalarSuffixRows
import TerminalLiftM31Exact
import ScalarLaneExecution
import SelectorValueLanePreprocessRangeValues
import SameBoxedRowExact
import R0P.Asset
import InitialArrayWrites
import EqualityValueAdapter

/-! Complete source scalar producer at the tail of semantic_packed.
Actual public M31 bounds remain explicit; all operation-success and scalar
residual identities are derived from one canonical point and openings.z. -/
set_option autoImplicit false
namespace AspisR1.ScalarSuffixExecution
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ScalarSuffixRows
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CanonicalArray {N : Usize} (a : Array QM N) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev modelVariant := AspisR1.OccupancyExpectedBridge.modelVariant
abbrev P := AspisR1.TerminalLiftM31Exact.P

def amountValue (p : Public) : U32 := p.withdrawal_amount.getD 0#u32

def exactAmount (p : Public) : Option ExactQM := p.withdrawal_amount.map (fun m => (m.val : ExactQM))

private theorem unwrap_amount (o : Option U32) :
    lift (core.option.Option.unwrap_or o 0#u32) = .ok (o.getD 0#u32) := by
  cases o <;> rfl

private theorem amount_present (o : Option U32) : core.option.Option.is_some o = o.isSome := by
  cases o <;> rfl

private theorem exactAmount_getD (p : Public) :
    (amountValue p).val = (p.withdrawal_amount.getD 0#u32).val := rfl

private theorem cast_amount (o : Option U32) :
    ((o.getD 0#u32).val : ExactQM) = (o.map (fun m => (m.val : ExactQM))).getD 0 := by
  cases o <;> simp only [Option.getD_none, Option.getD_some, Option.map_none, Option.map_some]
  rfl

private theorem mapped_presence (o : Option U32) :
    (o.map (fun m => (m.val : ExactQM))).isSome = o.isSome := by
  cases o <;> rfl

private theorem read_z (openings : Openings) (i : Usize) (hi : i.val < 16)
    (hz : CanonicalArray openings.z) :
    ∃ q, Array.index_usize openings.z i = .ok q ∧ CurrentCanonicalQM q ∧
      decode q = (exactOpenings openings).z ⟨i.val, hi⟩ := by
  have hzCells : ∀ j : Fin 16, CurrentCanonicalQM (AspisR1.AbsorptionCallback.sourceCell openings.z j) := by
    intro j
    exact hz ⟨j.val, by simpa using j.isLt⟩
  obtain ⟨q, hread, hcq, hvalue⟩ := AspisR1.InitialArrayWrites.read16_success openings.z i hi hzCells
  refine ⟨q, hread, hcq, ?_⟩
  rw [hvalue]
  rfl

attribute [local irreducible] AspisR1.SelectorValueLaneModelComposition.pointSelector R0P.assetScalarLanes

theorem source_values (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hasset : public1.asset_id.val < P)
    (hamount : (amountValue public1).val < P) :
    ∃ values : Array QM 2#usize,
      AspisR1ScalarSuffixCandidate.scalar_values public1 openings selectors = .ok values ∧
      CanonicalArray values ∧
      values.val.map decode =
        R0P.assetScalarLanes (modelVariant public1.variant) (exactAmount public1).isSome
          (pointSelector point 44 * ((exactOpenings openings).z 1 - (public1.asset_id.val : ExactQM)))
          (pointSelector point 508 * ((exactOpenings openings).z 1 - (public1.asset_id.val : ExactQM)))
          (pointSelector point 460 * ((exactOpenings openings).z 1 - (public1.asset_id.val : ExactQM)))
          (pointSelector point 1010 * ((exactOpenings openings).z 10 - (exactAmount public1).getD 0)) := by
  obtain ⟨z1, hz1, hcz1, hvz1⟩ := read_z openings 1#usize (by scalar_tac) hz
  obtain ⟨asset, hliftAsset, hcAsset, hvAsset⟩ := AspisR1.TerminalLiftM31Exact.lift_source_exact public1.asset_id hasset
  obtain ⟨difference, hdiff, hcDiff, hvDiff⟩ := AspisR1.EqualityValueAdapter.current_qm_sub_exact z1 asset hcz1 hcAsset
  change decode difference = decode z1 - decode asset at hvDiff
  obtain ⟨sel44, hs44, hc44, hv44⟩ := AspisR1.SameBoxedRowExact.row_success point selectors 44#usize (by scalar_tac) hpoint hbox
  obtain ⟨input, hinput, hcInput, hvInput⟩ := current_qm_mul_exact sel44 difference hc44 hcDiff
  obtain ⟨sel508, hs508, hc508, hv508⟩ := AspisR1.SameBoxedRowExact.row_success point selectors 508#usize (by scalar_tac) hpoint hbox
  obtain ⟨output, houtput, hcOutput, hvOutput⟩ := current_qm_mul_exact sel508 difference hc508 hcDiff
  obtain ⟨sel460, hs460, hc460, hv460⟩ := AspisR1.SameBoxedRowExact.row_success point selectors 460#usize (by scalar_tac) hpoint hbox
  obtain ⟨privateTerm, hprivate, hcPrivate, hvPrivate⟩ := current_qm_mul_exact sel460 difference hc460 hcDiff
  obtain ⟨sel1010, hs1010, hc1010, hv1010⟩ := AspisR1.SameBoxedRowExact.row_success point selectors 1010#usize (by scalar_tac) hpoint hbox
  obtain ⟨z10, hz10, hcz10, hvz10⟩ := read_z openings 10#usize (by scalar_tac) hz
  obtain ⟨amount, hliftAmount, hcAmount, hvAmount⟩ := AspisR1.TerminalLiftM31Exact.lift_source_exact (amountValue public1) hamount
  obtain ⟨withdrawDiff, hwdiff, hcWDiff, hvWDiff⟩ := AspisR1.EqualityValueAdapter.current_qm_sub_exact z10 amount hcz10 hcAmount
  change decode withdrawDiff = decode z10 - decode amount at hvWDiff
  obtain ⟨withdrawTerm, hwithdraw, hcWithdraw, hvWithdraw⟩ := current_qm_mul_exact sel1010 withdrawDiff hc1010 hcWDiff
  obtain ⟨values, hvalues, hcValues, hvValues⟩ := AspisR1.ScalarLaneExecution.source_success
    public1.variant public1.withdrawal_amount.isSome input output privateTerm withdrawTerm
    hcInput hcOutput hcPrivate hcWithdraw
  have hunwrap : lift (core.option.Option.unwrap_or public1.withdrawal_amount 0#u32) = .ok (amountValue public1) := unwrap_amount public1.withdrawal_amount
  simp only [AspisR1.ScalarLaneExecution.source] at hvalues
  refine ⟨values, ?_, hcValues, ?_⟩
  · unfold AspisR1ScalarSuffixCandidate.scalar_values
    dsimp only [HMul.hMul, HAdd.hAdd]
    simp only [hz1, bind_tc_ok, hliftAsset,
      hdiff, mul_two_sixteen, add_twelve_32, hs44, hinput, mul_31_sixteen,
      add_twelve_496, hs508, houtput, mul_28_sixteen, add_twelve_448, hs460,
      hprivate, hunwrap, mul_value_aux, add_two_1008,
      hs1010, hz10, hliftAmount, hwdiff, hwithdraw, amount_present,
      hvalues]
  · rw [hvValues, hvInput, hvOutput, hvPrivate, hvWithdraw, hvDiff, hvWDiff,
      hvz1, hvz10, hvAsset, hvAmount, hv44, hv508, hv460, hv1010]
    simp only [exactAmount, amountValue, cast_amount, mapped_presence]
    all_goals
      simp only [pointSelector, AspisR1.SameBoxedRowExact.pointSelector, modelVariant,
        AspisR1.ScalarLaneExecution.modelVariant,
        show (44#usize).val = 44 from by scalar_tac,
        show (508#usize).val = 508 from by scalar_tac,
        show (460#usize).val = 460 from by scalar_tac,
        show (1010#usize).val = 1010 from by scalar_tac,
        show (1#usize).val = 1 from by scalar_tac,
        show (10#usize).val = 10 from by scalar_tac]
    all_goals rfl

#print axioms source_values
end
end AspisR1.ScalarSuffixExecution
