import AspisR1TerminalDigestBindingCandidate.R0PBridge
import SameBoxedRowExact
import SemanticPublicModel
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisR1.DigestFixedBinding
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

def decoded (a : Array QM 8#usize) : R0P.Digest ExactQM :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (cellAt a j.val)

def openedModel (a : Array QM 16#usize) : Fin 16 → ExactQM :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (openedAt a j.val)

/-- The repeated checked-row and zero-offset binding fragment of the wrapper. -/
def bindBlock (initial : Array QM 8#usize) (opened : Array QM 16#usize)
    (selectors : Selectors) (block : Usize) (expected : Array M31 8#usize) :
    Result (Array QM 8#usize) := do
  let base ← block * 16#usize
  let row ← base + 11#usize
  let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors row
  AspisR1TerminalDigestBindingCandidate.add_digest_binding initial q opened 0#usize expected false

theorem false_target (expected : Array M31 8#usize) (j : Fin 8) :
    (targetValue expected false j.val : ExactQM) =
      SemanticPublicModel.digest expected j := by
  simp only [targetValue, j.isLt, _root_.dite_true, Bool.false_eq_true, false_and, if_false,
    SemanticPublicModel.digest]

/-- No checked-arithmetic, selector-row or binding success is assumed. -/
theorem bindBlock_success (point : Array QM 10#usize) (selectors : Selectors)
    (initial : Array QM 8#usize) (opened : Array QM 16#usize)
    (block : Usize) (expected : Array M31 8#usize)
    (hblock : block.val < 64)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hinitial : CanonicalArray initial) (hopened : CanonicalArray opened)
    (hexpected : ∀ j : Fin 8,
      (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
        AspisR1.ExtractedMaskTowerAdd.P) :
    ∃ out : Array QM 8#usize,
      bindBlock initial opened selectors block expected = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 8, decoded out j = R0P.digestAddBinding (decoded initial)
        (pointSelector point ⟨block.val * 16 + 11, by omega⟩)
        (openedModel opened) 0 (SemanticPublicModel.digest expected) j := by
  have hmul : (block * 16#usize : Result Usize) ⦃base => base.val = block.val * 16⦄ := by
    apply UScalar.mul_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨base, hbase, hbval⟩ := WP.spec_imp_exists hmul
  have hadd : (base + 11#usize : Result Usize) ⦃row => row.val = base.val + 11⦄ := by
    apply UScalar.add_spec
    have hmax := Usize.cMax_bound_concrete.1
    scalar_tac
  obtain ⟨row, hrow, hrval⟩ := WP.spec_imp_exists hadd
  have hrbound : row.val < 1024 := by omega
  obtain ⟨q, hq, hcq, hqmodel⟩ :=
    SameBoxedRowExact.row_success point selectors row hrbound hpoint hbox
  obtain ⟨out, hout, hcout, hvalues⟩ :=
    AspisR1TerminalDigestBindingCandidate.R0PBridge.add_digest_binding_is_r0p
      initial q opened 0#usize expected false (by decide) hinitial hcq hopened hexpected
  refine ⟨out, ?_, hcout, ?_⟩
  · unfold bindBlock
    rw [hbase]
    simp only [bind_tc_ok]
    rw [hrow]
    simp only [bind_tc_ok]
    rw [hq]
    simp only [bind_tc_ok]
    exact hout
  · intro j
    have hrowid : (⟨row.val, hrbound⟩ : Fin 1024) =
        ⟨block.val * 16 + 11, by omega⟩ := by
      apply Fin.ext
      change row.val = block.val * 16 + 11
      rw [hrval, hbval]
    have ht : (fun i : Fin 8 => (targetValue expected false i.val : ExactQM)) =
        SemanticPublicModel.digest expected := funext (false_target expected)
    have h := hvalues j
    rw [hqmodel, hrowid, ht] at h
    exact h

#print axioms false_target
#print axioms bindBlock_success
end
end AspisR1.DigestFixedBinding
