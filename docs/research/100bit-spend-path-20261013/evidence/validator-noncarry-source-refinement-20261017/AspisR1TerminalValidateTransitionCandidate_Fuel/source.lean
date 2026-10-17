import TerminalValidateTransitionStepCarry
import OccupancyRangeTraversal
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate.Fuel
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalValidateTransitionCandidate
abbrev Usize := UScalar UScalarTy.Usize
abbrev Range := core.ops.range.Range Usize
abbrev M31 := field.M31
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact

/-- Every row in the unconsumed range of a successful source loop has the
actual candidate frontier read equal to the source's exact row operand. -/
theorem loop_row_success_fuel
    (public1 : Public) (iter : Range) (carry : Usize) (fuel : Nat)
    (hend : iter.end.val = 20) (hspan : iter.start.val + fuel = 20)
    (hsuccess : validate_transition_loop public1 iter carry = .ok (.Ok ())) :
    ∀ level : Usize, iter.start.val ≤ level.val → level.val < iter.end.val →
      level ≠ carry →
      ∃ iterAfter expected,
        Array.index_usize public1.transition.candidate_afterstate.next_frontier level = .ok expected ∧
        expectedWithIter public1 iterAfter level carry = .ok (iterAfter, expected) := by
  induction fuel generalizing iter with
  | zero =>
      intro level hlo hhi hne
      have hstart : iter.start.val = iter.end.val := by omega
      omega
  | succ fuel ih =>
      intro level hlo hhi hne
      have hlt : iter.start.val < iter.end.val := by omega
      have hlevel20 : level.val < 20 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 20 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 20 := by omega
      by_cases hstartCarry : iter.start = carry
      · have hcarryLt : carry < 20#usize := by
          rw [← hstartCarry]
          change iter.start.val < 20
          omega
        obtain ⟨iterNext, hnextCarry, hrec⟩ :=
          carry_step_success public1 iter carry hlt hstartCarry hcarryLt hsuccess
        have hnextEq : iterNext = iter1 := by
          have hp := Result.ok.inj (hnextCarry.symm.trans hnext)
          exact congrArg Prod.snd hp
        have hlevelAfter : iter1.start.val ≤ level.val := by
          have hstart1val : iter1.start.val = iter.start.val + 1 := hstart1
          have hneval : level.val ≠ carry.val := by
            intro heq
            apply hne
            exact UScalar.eq_of_val_eq heq
          have hstartval : iter.start.val = carry.val := congrArg UScalar.val hstartCarry
          omega
        have hhi1 : level.val < iter1.end.val := by simpa [hend1] using hhi
        obtain ⟨iterAfter, expected, hread, hexpected⟩ :=
          ih iter1 hend1' hspan1 (by simpa [hnextEq] using hrec)
            level hlevelAfter hhi1 hne
        exact ⟨iterAfter, expected, hread, hexpected⟩
      · obtain ⟨iterNext, expected0, hnextNon, hexpected0, hread0, hrec⟩ :=
          noncarry_step_success public1 iter carry hlt hstartCarry hsuccess
        have hnextEq : iterNext = iter1 := by
          have hp := Result.ok.inj (hnextNon.symm.trans hnext)
          exact congrArg Prod.snd hp
        by_cases hsame : level.val = iter.start.val
        · have hlevelEq : level = iter.start := UScalar.eq_of_val_eq hsame
          subst level
          have hread : Array.index_usize public1.transition.candidate_afterstate.next_frontier
              iter.start = .ok expected0 := hread0
          exact ⟨iterNext, expected0, hread, hexpected0⟩
        · have hlevelAfter : iter1.start.val ≤ level.val := by
            have hstart1val : iter1.start.val = iter.start.val + 1 := hstart1
            omega
          have hhi1 : level.val < iter1.end.val := by simpa [hend1] using hhi
          obtain ⟨iterAfter, expected, hread, hexpected⟩ :=
            ih iter1 hend1' hspan1 (by simpa [hnextEq] using hrec)
              level hlevelAfter hhi1 hne
          exact ⟨iterAfter, expected, hread, hexpected⟩

#print axioms loop_row_success_fuel
end AspisR1TerminalValidateTransitionCandidate.Fuel
