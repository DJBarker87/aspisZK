import AspisR1.CopyLinkLoopFactor
import AspisR1.CopyLinkLoopModel
import ExtractedMaskHornerStep

/-! Actual full Copy loop traversal. The only loop measure is the remaining
number of literal registry records; source arithmetic/updates come from the
proved same-record step, and the model is a symbolic suffix fold. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkLoopFuel
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.CopyLinkWeightExact AspisR1.CopyLinkStepExact
open AspisR1.CopyEndpointExact AspisR1.CopyRegistryModel
open AspisR1.CopyLinkLoopFactor AspisR1.CopyLinkLoopModel
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

/-- The actual recursive source loop succeeds and agrees with the full
remaining registry fold, with no per-link execution or canonicality premises. -/
theorem loop_success_fuel (selectors : Selectors) (index : U64) (variant : Variant)
    (patterns : Array QM 14#usize) (pv pw cv cw : Array QM 2#usize)
    (cursor : Usize) (fuel : Nat) (hspan : cursor.val + fuel = 136)
    (hpatterns : CanonicalArray patterns)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hpv : CanonicalArray pv) (hpw : CanonicalArray pw)
    (hcv : CanonicalArray cv) (hcw : CanonicalArray cw) :
    ∃ pvOut pwOut cvOut cwOut,
      loopFn selectors index variant patterns pv pw cv cw cursor =
        .ok (pvOut,pwOut,cvOut,cwOut) ∧
      CanonicalArray pvOut ∧ CanonicalArray pwOut ∧
      CanonicalArray cvOut ∧ CanonicalArray cwOut ∧
      modelRow pvOut pwOut cvOut cwOut =
        remaining index.val (modelVariant variant) (decodedCells patterns)
          (modelSelectors selectors) cursor.val (modelRow pv pw cv cw) := by
  have hcount : count.val = 136 := by
    unfold count AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1
    scalar_tac
  induction fuel generalizing cursor pv pw cv cw with
  | zero =>
    have hcursor : cursor.val = 136 := by omega
    have hstop : ¬ cursor < count := by
      change ¬ cursor.val < count.val
      omega
    refine ⟨pv,pw,cv,cw,?_,hpv,hpw,hcv,hcw,?_⟩
    · unfold loopFn
      rw [AspisR1CopyLinkLoopCandidate.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop.eq_def]
      simp [hstop]
    · rw [hcursor]
      exact (remaining_end index.val (modelVariant variant) (decodedCells patterns)
        (modelSelectors selectors) (modelRow pv pw cv cw)).symm
  | succ fuel ih =>
    have hcursor : cursor.val < 136 := by omega
    have hlt : cursor < count := by
      change cursor.val < count.val
      omega
    let pos : Fin 136 := ⟨cursor.val,hcursor⟩
    let link := rawAt pos
    have hread : Array.index_usize registry cursor = .ok link := by
      simpa [link, rawAt, pos] using
        AspisR1.ExtractedMaskHornerStep.array_index_usize_ok registry cursor
          (by simpa using hcursor)
    have hmem : link ∈ registry.val := by
      exact List.getElem_mem _
    obtain ⟨htag,hkind,hlevel,hb⟩ := AspisR1.CopyRegistryBounds.member_bounds link hmem
    obtain ⟨pv1,pw1,cv1,cw1,hstep,hcpv,hcpw,hccv,hccw,hmodel⟩ :=
      step_success link index variant patterns selectors pv pw cv cw
        hkind hlevel hb htag hpatterns hhigh hlow hpv hpw hcv hcw
    have hmodelLink : modelLink link hkind hb = modelAt pos := by rfl
    rw [hmodelLink] at hmodel
    obtain ⟨cursor1,hnext,hnextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := cursor) (y := 1#usize) (by scalar_tac))
    have hnextVal : cursor1.val = cursor.val + 1 := by simpa using hnextValue
    have hspan1 : cursor1.val + fuel = 136 := by omega
    obtain ⟨pvOut,pwOut,cvOut,cwOut,hrec,hcpvOut,hcpwOut,hccvOut,hccwOut,hrecModel⟩ :=
      ih pv1 pw1 cv1 cw1 cursor1 hspan1 hcpv hcpw hccv hccw
    refine ⟨pvOut,pwOut,cvOut,cwOut,?_,hcpvOut,hcpwOut,hccvOut,hccwOut,?_⟩
    · rw [loop_step_eq selectors index variant patterns pv pw cv cw cursor link hlt hread]
      simp only [hstep, bind_tc_ok, hnext]
      exact hrec
    · calc
        modelRow pvOut pwOut cvOut cwOut =
          remaining index.val (modelVariant variant) (decodedCells patterns)
            (modelSelectors selectors) cursor1.val (modelRow pv1 pw1 cv1 cw1) := hrecModel
        _ = remaining index.val (modelVariant variant) (decodedCells patterns)
            (modelSelectors selectors) (cursor.val + 1)
            (modelStep (modelRow pv pw cv cw) (modelAt pos) index.val
              (modelVariant variant) (decodedCells patterns) (modelSelectors selectors)) := by
          rw [hnextVal, hmodel]
        _ = remaining index.val (modelVariant variant) (decodedCells patterns)
            (modelSelectors selectors) cursor.val (modelRow pv pw cv cw) :=
          (remaining_step index.val (modelVariant variant) (decodedCells patterns)
            (modelSelectors selectors) pos (modelRow pv pw cv cw)).symm

/-- The complete136-link loop from source cursor0 equals the retained
registry fold, for the same input arrays, patterns, selectors, index and variant. -/
theorem loop_success (selectors : Selectors) (index : U64) (variant : Variant)
    (patterns : Array QM 14#usize) (pv pw cv cw : Array QM 2#usize)
    (hpatterns : CanonicalArray patterns)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hpv : CanonicalArray pv) (hpw : CanonicalArray pw)
    (hcv : CanonicalArray cv) (hcw : CanonicalArray cw) :
    ∃ pvOut pwOut cvOut cwOut,
      loopFn selectors index variant patterns pv pw cv cw 0#usize =
        .ok (pvOut,pwOut,cvOut,cwOut) ∧
      CanonicalArray pvOut ∧ CanonicalArray pwOut ∧
      CanonicalArray cvOut ∧ CanonicalArray cwOut ∧
      modelRow pvOut pwOut cvOut cwOut =
        R0P.copyLinks.foldl
          (fun acc link => modelStep acc link index.val (modelVariant variant)
            (decodedCells patterns) (modelSelectors selectors)) (modelRow pv pw cv cw) := by
  obtain ⟨pvOut,pwOut,cvOut,cwOut,hr,hpvOut,hpwOut,hcvOut,hcwOut,hmodel⟩ :=
    loop_success_fuel selectors index variant patterns pv pw cv cw 0#usize 136
      (by scalar_tac) hpatterns hhigh hlow hpv hpw hcv hcw
  refine ⟨pvOut,pwOut,cvOut,cwOut,hr,hpvOut,hpwOut,hcvOut,hcwOut,?_⟩
  have hz : (0#usize : Usize).val = 0 := by scalar_tac
  rw [hz, remaining_zero] at hmodel
  exact hmodel

#print axioms loop_success
#print axioms loop_success_fuel
end
end AspisR1.CopyLinkLoopFuel
