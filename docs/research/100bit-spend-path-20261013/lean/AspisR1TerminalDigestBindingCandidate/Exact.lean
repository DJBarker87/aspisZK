import AspisR1TerminalDigestBindingCandidate.Source
import ExtractedMaskQM31Exact
import EqualityValueAdapter
import TerminalLiftM31Exact

set_option autoImplicit false

namespace AspisR1TerminalDigestBindingCandidate.Exact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

/-- One exact source lane of `add_digest_binding`: after lifting the selected
M31 target, the current QM31 sub/mul/add chain succeeds, remains canonical,
and denotes the displayed tower expression. -/
theorem lane_arithmetic_exact
    (old selector opened : QM) (target : M31)
    (hold : Canonical old) (hselector : Canonical selector)
    (hopened : Canonical opened) (htarget : target.val < AspisR1.ExtractedMaskTowerAdd.P) :
    ∃ lifted difference scaled updated,
      pool_v1.pair_forest_semantic_terminal.lift_m31 target = .ok lifted ∧
      field.QM31.sub opened lifted = .ok difference ∧
      field.QM31.mul selector difference = .ok scaled ∧
      field.QM31.add old scaled = .ok updated ∧
      Canonical updated ∧
      AspisR1.ExtractedMaskQM31Exact.decode updated =
        AspisR1.ExtractedMaskQM31Exact.decode old +
          AspisR1.ExtractedMaskQM31Exact.decode selector *
            (AspisR1.ExtractedMaskQM31Exact.decode opened - (target.val : ExactQM)) := by
  obtain ⟨lifted, hlift, hliftCanonical, hliftDecode⟩ :=
    AspisR1.TerminalLiftM31Exact.lift_source_exact target (by
      simpa [AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P] using htarget)
  obtain ⟨difference, hsub, hdifferenceCanonical, hdifference⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact opened lifted hopened hliftCanonical
  obtain ⟨scaled, hmul, hscaledCanonical, hscaled⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact selector difference
      hselector hdifferenceCanonical
  obtain ⟨updated, hadd, hupdatedCanonical, hupdated⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact old scaled
      hold hscaledCanonical
  refine ⟨lifted, difference, scaled, updated, hlift, hsub, hmul, hadd,
    hupdatedCanonical, ?_⟩
  have hdifference' : AspisR1.ExtractedMaskQM31Exact.decode difference =
      AspisR1.ExtractedMaskQM31Exact.decode opened -
        AspisR1.ExtractedMaskQM31Exact.decode lifted := by
    simpa [AspisR1.EqualityValueAdapter.decode] using hdifference
  change AspisR1.ExtractedMaskQM31Exact.decode updated =
      AspisR1.ExtractedMaskQM31Exact.decode old +
        AspisR1.ExtractedMaskQM31Exact.decode selector *
          (AspisR1.ExtractedMaskQM31Exact.decode opened - (target.val : ExactQM))
  calc
    AspisR1.ExtractedMaskQM31Exact.decode updated =
        AspisR1.ExtractedMaskQM31Exact.decode old +
          AspisR1.ExtractedMaskQM31Exact.decode scaled := hupdated
    _ = AspisR1.ExtractedMaskQM31Exact.decode old +
          (AspisR1.ExtractedMaskQM31Exact.decode selector *
            AspisR1.ExtractedMaskQM31Exact.decode difference) := by rw [hscaled]
    _ = AspisR1.ExtractedMaskQM31Exact.decode old +
          (AspisR1.ExtractedMaskQM31Exact.decode selector *
            (AspisR1.ExtractedMaskQM31Exact.decode opened - (target.val : ExactQM))) := by
      rw [hdifference', hliftDecode]


/-- The exact source right-tweak sub-block at one digest lane. -/
def targetAfterLane (lane : Usize) (expected : M31) (rightTweak : Bool) :
    Result M31 := do
  if rightTweak then do
    let i ← lane + 1#usize
    if i = poseidon2.DIGEST_ELEMS then
      field.M31.add expected poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
    else ok expected
  else ok expected

theorem targetAfterLane_success
    (lane : Usize) (expected : M31) (rightTweak : Bool)
    (hlane : lane.val < 8)
    (hexpected : expected.val < AspisR1.ExtractedMaskTowerAdd.P) :
    ∃ target, targetAfterLane lane expected rightTweak = .ok target ∧
      target.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      target.val = if rightTweak = true ∧ lane.val = 7 then
        (expected.val + poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK.val) %
          AspisR1.ExtractedMaskTowerAdd.P
      else expected.val := by
  by_cases hright : rightTweak
  · have hspec : (lane + 1#usize : Result Usize) ⦃i => i.val = lane.val + 1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨i, hadd, hi⟩ := Aeneas.Std.WP.spec_imp_exists hspec
    by_cases heq : i = poseidon2.DIGEST_ELEMS
    · have hlaneEq : lane.val = 7 := by
        have hi' : i.val = 8 := by simpa [poseidon2.DIGEST_ELEMS] using congrArg (fun x : Usize => x.val) heq
        omega
      have htweak : poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK.val <
          AspisR1.ExtractedMaskTowerAdd.P := by
        norm_num [poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK,
          AspisR1.ExtractedMaskTowerAdd.P,
          AspisR1.ExtractedMaskM31AddSub.P]
      obtain ⟨target, htarget, hvalue, hcanon⟩ :=
        AspisR1.ExtractedMaskM31AddSub.current_add_mod expected
          poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK hexpected htweak
      refine ⟨target, ?_, hcanon, ?_⟩
      · simp [targetAfterLane, hright, hadd, heq, htarget]
      · simp [hright, hlaneEq, hvalue]
    · refine ⟨expected, ?_, hexpected, ?_⟩
      · simp [targetAfterLane, hright, hadd, heq]
      · have hnot : lane.val ≠ 7 := by
          intro h7
          apply heq
          apply UScalar.eq_of_val_eq
          simp [hi, h7, poseidon2.DIGEST_ELEMS]
        simp [hright, hnot]
  · exact ⟨expected, by simp [targetAfterLane, hright], hexpected, by simp [hright]⟩

#print axioms lane_arithmetic_exact
#print axioms targetAfterLane_success

end AspisR1TerminalDigestBindingCandidate.Exact
