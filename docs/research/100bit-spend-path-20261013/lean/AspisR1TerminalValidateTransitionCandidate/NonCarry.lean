import AspisR1TerminalValidateTransitionCandidate.Fuel
import AspisR1TerminalValidateTransitionCandidate.ExpectedAt
import AspisR1TerminalValidateTransitionCandidate.RowMeaning
import BoundedControlCarry
import SemanticPublicModel
import R0P.Digest
import Aeneas.Tactic

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.NonCarry
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalValidateTransitionCandidate
abbrev Usize := UScalar UScalarTy.Usize
abbrev Range := core.ops.range.Range Usize
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact

/-- A successful real bounded-carry call and the successful exact validation
loop imply the full non-carry frontier shape for the same SemanticPublic. -/
theorem validate_loop_success_noncarry_shape
    (public1 : Public) (carry : Usize)
    (hcarryRun : AspisBoundedControl.bounded_carry
      public1.transition.live_snapshot.next_pair_index = .ok carry)
    (hsuccess : validate_transition_loop public1
      { start := 0#usize, «end» := 20#usize } carry = .ok (.Ok ())) :
    ∀ level : Fin 20,
      level.val ≠ R0P.digestCarry
        (AspisR1.SemanticPublicModel.exactPublic public1).nextPairIndex →
      (AspisR1.SemanticPublicModel.exactPublic public1).nextFrontier level =
        if level.val < R0P.digestCarry
              (AspisR1.SemanticPublicModel.exactPublic public1).nextPairIndex ∨
            R0P.digestBitZero (AspisR1.SemanticPublicModel.exactPublic public1) level
        then AspisR1TerminalValidateTransitionCandidate.RowMeaning.frozenEmptyModel level.castSucc
        else (AspisR1.SemanticPublicModel.exactPublic public1).snapshotFrontier level := by
  obtain ⟨carryOut, hbounded, hcarryVal, _⟩ :=
    AspisBoundedControl.Carry.bounded_carry_is_digestCarry
      public1.transition.live_snapshot.next_pair_index
  have hcarryEq : carryOut = carry := Result.ok.inj (hbounded.symm.trans hcarryRun)
  have hcarryModel : carry.val = R0P.digestCarry
      public1.transition.live_snapshot.next_pair_index.val := by
    rw [← hcarryEq]
    exact hcarryVal
  let iter : Range := { start := 0#usize, «end» := 20#usize }
  have hend : iter.end.val = 20 := by dsimp [iter]; scalar_tac
  have hspan : iter.start.val + 20 = 20 := by dsimp [iter]; scalar_tac
  intro level hlevelNe
  let levelU : Usize := UScalar.ofNatCore level.val (by scalar_tac)
  have hlevelUVal : levelU.val = level.val := by simp [levelU]
  have hlevelU20 : levelU.val < 20 := by simpa [hlevelUVal] using level.isLt
  have hstart : iter.start.val ≤ levelU.val := by dsimp [iter]; simp [hlevelUVal]
  have hbelow : levelU.val < iter.end.val := by simpa [hend] using hlevelU20
  have hneU : levelU ≠ carry := by
    intro heq
    apply hlevelNe
    calc
      level.val = levelU.val := hlevelUVal.symm
      _ = carry.val := congrArg UScalar.val heq
      _ = R0P.digestCarry
        public1.transition.live_snapshot.next_pair_index.val := hcarryModel
  obtain ⟨iterAfter, expected, hread, hexpected⟩ :=
    AspisR1TerminalValidateTransitionCandidate.Fuel.loop_row_success_fuel
      public1 iter carry 20 hend hspan (by simpa [iter] using hsuccess)
      levelU hstart hbelow hneU
  have hexpectedAt :=
    AspisR1TerminalValidateTransitionCandidate.ExpectedAt.expectedAt_of_expectedWithIter
      public1 iterAfter levelU carry expected hexpected
  have hrow :=
    AspisR1TerminalValidateTransitionCandidate.RowMeaning.expectedAt_matches_noncarry_model
      public1 carry levelU (by simpa [hlevelUVal] using level.isLt) expected hexpectedAt
  have hbound : levelU.val < public1.transition.candidate_afterstate.next_frontier.length := by
    simpa [public1.transition.candidate_afterstate.next_frontier.property,
      hlevelUVal] using level.isLt
  obtain ⟨q, hreadQ, hqvalue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec public1.transition.candidate_afterstate.next_frontier levelU hbound)
  have hExpectedQ : expected = q := Result.ok.inj (hread.symm.trans hreadQ)
  have hqvalue' : q = public1.transition.candidate_afterstate.next_frontier.val[levelU.val]'(by
      simpa [public1.transition.candidate_afterstate.next_frontier.property] using hbound) := by
    simpa using hqvalue
  have hExpectedCell : expected =
      public1.transition.candidate_afterstate.next_frontier.val[levelU.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using hbound) :=
    hExpectedQ.trans hqvalue'
  have hrow' : AspisR1.SemanticPublicModel.digest
      (public1.transition.candidate_afterstate.next_frontier.val[levelU.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using hbound)) =
      if levelU.val < R0P.digestCarry public1.transition.live_snapshot.next_pair_index.val ∨
          R0P.digestBitZero (AspisR1.SemanticPublicModel.exactPublic public1)
            ⟨levelU.val, by omega⟩
      then AspisR1TerminalValidateTransitionCandidate.RowMeaning.frozenEmptyModel
        ⟨levelU.val, by omega⟩
      else (AspisR1.SemanticPublicModel.exactPublic public1).snapshotFrontier
        ⟨levelU.val, by omega⟩ := by
    simpa [hExpectedCell, hcarryModel, AspisR1.SemanticPublicModel.exactPublic] using hrow
  have hlevelFin : (⟨levelU.val, hlevelU20⟩ : Fin 20) = level := by
    apply Fin.ext
    exact hlevelUVal
  have hlevel21 : (⟨levelU.val, by omega⟩ : Fin 21) = level.castSucc := by
    apply Fin.ext
    simp [hlevelUVal]
  rw [hlevel21] at hrow'
  rw [← hlevelFin]
  change AspisR1.SemanticPublicModel.digest
      (public1.transition.candidate_afterstate.next_frontier.val[levelU.val]'(by
        simpa [public1.transition.candidate_afterstate.next_frontier.property] using hlevelU20)) = _
  simpa [hlevelUVal, hlevel21, AspisR1.SemanticPublicModel.exactPublic] using hrow'

#print axioms validate_loop_success_noncarry_shape
end AspisR1TerminalValidateTransitionCandidate.NonCarry
