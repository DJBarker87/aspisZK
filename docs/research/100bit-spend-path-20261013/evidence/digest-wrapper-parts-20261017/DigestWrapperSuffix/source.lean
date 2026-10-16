import DigestFixedPrefix
import BoundedControlCarry

/-! The next-root/carry suffix for the bounded-carry source candidate.
The prefix, outer loop and release-artifact correspondence remain separate. -/
set_option autoImplicit false
namespace AspisR1.DigestWrapperSuffix
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
open AspisR1.DigestFixedBinding
open AspisR1.DigestFixedPrefix

def run (initial : Array QM 8#usize) (opened : Array QM 16#usize)
    (selectors : Selectors) (public1 : Public) : Result (Array QM 8#usize) := do
  let d1 ← bindBlock initial opened selectors 53#usize
    public1.transition.candidate_afterstate.next_root
  let carry ← AspisBoundedControl.bounded_carry public1.transition.live_snapshot.next_pair_index
  if carry < 20#usize then
    let block ← 33#usize + carry
    let base ← block * 16#usize
    let row ← base + 11#usize
    let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors row
    let expected ← Array.index_usize public1.transition.candidate_afterstate.next_frontier carry
    AspisR1TerminalDigestBindingCandidate.add_digest_binding d1 q opened 0#usize expected false
  else .ok d1

@[irreducible] def model (point : Array QM 10#usize) (opened : Array QM 16#usize)
    (public1 : Public) (initial : R0P.Digest ExactQM) : R0P.Digest ExactQM :=
  let d1 := step point opened 53 public1.transition.candidate_afterstate.next_root initial
  if hc : R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val < 20 then
    step point opened ⟨33 + R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val,
      by omega⟩
      (public1.transition.candidate_afterstate.next_frontier.val[
        R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val]'(by
          simpa [public1.transition.candidate_afterstate.next_frontier.property] using hc)) d1
  else d1

attribute [local irreducible] R0P.digestAddBinding
  AspisR1.SelectorValueLaneModelComposition.pointSelector

theorem source_success (point : Array QM 10#usize) (selectors : Selectors)
    (initial : Array QM 8#usize) (opened : Array QM 16#usize) (public1 : Public)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hinitial : CanonicalArray initial) (hopened : CanonicalArray opened)
    (hroot : DigestWordsCanonical public1.transition.candidate_afterstate.next_root)
    (hfrontier : ∀ j : Fin 20, DigestWordsCanonical
      (public1.transition.candidate_afterstate.next_frontier.val[j.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using j.isLt))) :
    ∃ out, run initial opened selectors public1 = .ok out ∧ CanonicalArray out ∧
      decoded out = model point opened public1 (decoded initial) := by
  obtain ⟨d1, h1, hc1, hv1⟩ := bindBlock_success point selectors initial opened 53#usize
    public1.transition.candidate_afterstate.next_root (by decide)
    hpoint hbox hinitial hopened hroot
  have h1m : decoded d1 = step point opened 53
      public1.transition.candidate_afterstate.next_root (decoded initial) := by
    unfold step
    exact funext hv1
  obtain ⟨carry, hcarry, hcval, hcle⟩ :=
    AspisBoundedControl.Carry.bounded_carry_is_digestCarry
      public1.transition.live_snapshot.next_pair_index
  by_cases hc : carry.val < 20
  · have hclt : carry < 20#usize := hc
    have hmodelcarry : R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val < 20 := by
      omega
    have hblockSpec : (33#usize + carry : Result Usize) ⦃ b => b.val = 33 + carry.val ⦄ := by
      apply UScalar.add_spec
      have hmax := Usize.cMax_bound_concrete.1
      scalar_tac
    obtain ⟨block, hb, hbval⟩ := WP.spec_imp_exists hblockSpec
    have hb64 : block.val < 64 := by omega
    let expected := public1.transition.candidate_afterstate.next_frontier.val[carry.val]'(by
      simpa [public1.transition.candidate_afterstate.next_frontier.property] using hc)
    have hread : Array.index_usize public1.transition.candidate_afterstate.next_frontier carry =
        .ok expected := by
      obtain ⟨value, hv, hvmodel⟩ := WP.spec_imp_exists
        (Array.index_usize_spec public1.transition.candidate_afterstate.next_frontier carry
          (by simpa [public1.transition.candidate_afterstate.next_frontier.property] using hc))
      rw [hv]
      congr 1
    have hcanonical : DigestWordsCanonical expected := hfrontier ⟨carry.val, hc⟩
    obtain ⟨out, ho, hco, hvo⟩ := bindBlock_success point selectors d1 opened block expected
      hb64 hpoint hbox hc1 hopened hcanonical
    refine ⟨out, ?_, hco, ?_⟩
    · unfold run
      rw [h1]
      simp only [bind_tc_ok]
      rw [hcarry]
      simp only [bind_tc_ok, if_pos hclt]
      rw [hb]
      simp only [bind_tc_ok]
      rw [hread]
      simp only [bind_tc_ok]
      exact ho
    · have hvmodel : decoded out = step point opened ⟨block.val, hb64⟩ expected (decoded d1) := by
        unfold step
        exact funext hvo
      rw [model, dif_pos hmodelcarry]
      rw [h1m] at hvmodel
      have hbf : (⟨block.val, hb64⟩ : Fin 64) =
          ⟨33 + R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val, by omega⟩ := by
        apply Fin.ext
        change block.val = 33 + R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val
        rw [hbval, hcval]
      rw [hbf] at hvmodel
      simpa only [expected, hcval] using hvmodel
  · have hclt : ¬ carry < 20#usize := hc
    have hmodelcarry : ¬ R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val < 20 := by
      omega
    refine ⟨d1, ?_, hc1, ?_⟩
    · unfold run
      rw [h1]
      simp only [bind_tc_ok]
      rw [hcarry]
      simp only [bind_tc_ok, if_neg hclt]
    · rw [model, dif_neg hmodelcarry]
      exact h1m

#print axioms source_success
end
end AspisR1.DigestWrapperSuffix
