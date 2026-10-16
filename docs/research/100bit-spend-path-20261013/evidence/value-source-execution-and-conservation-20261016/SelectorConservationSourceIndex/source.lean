import SelectorConservationTail

/-! Checked source index arithmetic for the conservation selector. This
removes the implicit assumption that the Rust expression 16*63+6 returns
the intended selector row before the conservation-tail proof is applied. -/
set_option autoImplicit false
namespace AspisR1.SelectorConservationSourceIndex
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorConservationTail
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM

def selectorIndex : Result Usize := do
  let base ← 16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  base + 6#usize

theorem selectorIndex_success : selectorIndex = .ok 1014#usize := by
  have hmul : (16#usize *
      pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK : Result Usize)
      ⦃ x => x.val = 16*63 ⦄ := by
    unfold pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
    apply Usize.mul_spec
    scalar_tac
  obtain ⟨base, hbase, hbval⟩ := WP.spec_imp_exists hmul
  have hadd : (base + 6#usize : Result Usize) ⦃ x => x.val = base.val+6 ⦄ := by
    apply Usize.add_spec
    rw [hbval]
    scalar_tac
  obtain ⟨row, hrow, hrval⟩ := WP.spec_imp_exists hadd
  have heq : row = 1014#usize := by
    apply UScalar.eq_of_val_eq
    rw [hrval, hbval]
    scalar_tac
  unfold selectorIndex
  simp only [hbase, bind_tc_ok, hrow, heq]

def run (selectors : Selectors) (packed : Array QM 24#usize)
    (z succ : Array QM 16#usize) : Result (Array QM 24#usize) := do
  let index ← selectorIndex
  let selector ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors index
  AspisR1.ValueConservationTail.run packed selector z succ

theorem run_eq_tail (selectors : Selectors) (packed : Array QM 24#usize)
    (z succ : Array QM 16#usize) (selector : QM)
    (hrow : pool_v1.pair_forest_copy_terminal.Selectors.row selectors 1014#usize =
      .ok selector) :
    run selectors packed z succ = AspisR1.ValueConservationTail.run packed selector z succ := by
  simp only [run, selectorIndex_success, bind_tc_ok, hrow]

theorem same_boxed_source_tail
    (point : Array QM 10#usize) (selectors : Selectors)
    (packed : Array QM 24#usize) (z succ : Array QM 16#usize)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point =
      .ok selectors)
    (hpacked : CanonicalArray packed) (hz : CanonicalArray z)
    (hsucc : CanonicalArray succ) :
    ∃ selector r0 r1 : QM, ∃ out : Array QM 24#usize,
      run selectors packed z succ = .ok out ∧ CanonicalArray out ∧
      CanonicalArray (Array.make 2#usize [r0, r1]) ∧
      decoded out = (fun j => decoded packed j +
        groupValue (Array.make 2#usize [r0, r1]) 82 j.val) ∧
      decode selector = pointSelector point 1014 ∧
      decode r0 = pointSelector point 1014 *
        ((decode (AspisR1.ValueConservationTail.cellAt z 0) -
          decode (AspisR1.ValueConservationTail.cellAt z 1)) -
            decode (AspisR1.ValueConservationTail.cellAt z 2)) ∧
      decode r1 = pointSelector point 1014 *
        (decode (AspisR1.ValueConservationTail.cellAt succ 0) -
          decode (AspisR1.ValueConservationTail.cellAt succ 1)) := by
  obtain ⟨selector, r0, r1, out, hrow, _hselector, hvalue, htail,
    hout, harray, hmodel, hv0, hv1⟩ :=
    same_boxed_conservation_tail point selectors packed z succ hpoint hbox hpacked hz hsucc
  exact ⟨selector, r0, r1, out,
    (run_eq_tail selectors packed z succ selector hrow).trans htail,
    hout, harray, hmodel, hvalue, hv0, hv1⟩

#print axioms selectorIndex_success
#print axioms run_eq_tail
#print axioms same_boxed_source_tail
end AspisR1.SelectorConservationSourceIndex
