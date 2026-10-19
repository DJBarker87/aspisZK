import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import AspisR1.TerminalV4ResultAndIndexSuccess
import AspisR1.TerminalV4SelectorLoopCanonical
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.TerminalV4SelectorMaskSumCanonical
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Values := Array QM 16#usize
abbrev Loop := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop
abbrev SelectorSum := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16

def valueCell (values : Values) (i : Fin 16) : QM :=
  values.val[i.val]'(by simpa [values.property] using i.isLt)

theorem zero_one_canonical : Canonical AspisR1SelectedMaskProbe.field.QM31.ZERO ∧ Canonical AspisR1SelectedMaskProbe.field.QM31.ONE := by
  constructor <;> unfold Canonical AspisR1.TerminalV4TowerAdd.CanonicalQM AspisR1.TerminalV4TowerAdd.CanonicalCM
  · simp [AspisR1SelectedMaskProbe.field.QM31.ZERO, AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P]
  · simp [AspisR1SelectedMaskProbe.field.QM31.ONE, AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P]

theorem selector_mask_sum_success_canonical (values : Values) (mask : U16) (out : QM)
    (hvalues : ∀ i : Fin 16, Canonical (valueCell values i))
    (hrun : SelectorSum values mask = .ok out) : Canonical out := by
  have h := hrun
  change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16 values mask = .ok out at h
  rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16] at h
  obtain ⟨count, hcount, hrest⟩ :=
    AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
      (core.num.U16.count_ones mask)
      (fun count => do
        let pair ← if count > 8#u32 then do
          let mask2 ← lift (~~~ mask)
          ok (mask2, true)
        else ok (mask, false)
        let sum ← if pair.2 then ok AspisR1SelectedMaskProbe.field.QM31.ONE else ok AspisR1SelectedMaskProbe.field.QM31.ZERO
        Loop values pair.1 pair.2 sum) out h
  obtain ⟨pair, hchoice, htail⟩ :=
    AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
      (if count > 8#u32 then do
        let mask2 ← lift (~~~ mask)
        ok (mask2, true)
       else ok (mask, false))
      (fun pair => do
        let sum ← if pair.2 then ok AspisR1SelectedMaskProbe.field.QM31.ONE else ok AspisR1SelectedMaskProbe.field.QM31.ZERO
        Loop values pair.1 pair.2 sum) out hrest
  by_cases hgt : count > 8#u32
  · simp only [if_pos hgt] at hchoice
    obtain ⟨mask2, hnot, hpair⟩ :=
      AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
        (lift (~~~ mask)) (fun mask2 => ok (mask2, true)) pair hchoice
    have hp : (mask2, true) = pair := Result.ok.inj hpair
    rcases pair with ⟨mask1, complement⟩
    have hmask1 : mask1 = mask2 := (congrArg Prod.fst hp).symm
    have hcomp : complement = true := (congrArg Prod.snd hp).symm
    subst mask1
    subst complement
    have hloop : Loop values mask2 true AspisR1SelectedMaskProbe.field.QM31.ONE = .ok out := by
      simp only [if_pos True.intro, bind_tc_ok] at htail
      exact htail
    exact AspisR1.TerminalV4SelectorLoopCanonical.loop_success_canonical
      values mask2 true AspisR1SelectedMaskProbe.field.QM31.ONE out hvalues zero_one_canonical.2 hloop
  · have hnotgt : ¬ count > 8#u32 := hgt
    simp only [if_neg hnotgt] at hchoice
    have hp : (mask, false) = pair := Result.ok.inj hchoice
    rcases pair with ⟨mask1, complement⟩
    have hmask1 : mask1 = mask := (congrArg Prod.fst hp).symm
    have hcomp : complement = false := (congrArg Prod.snd hp).symm
    subst mask1
    subst complement
    have hloop : Loop values mask false AspisR1SelectedMaskProbe.field.QM31.ZERO = .ok out := by
      simpa only [if_neg (by decide : ¬ (false = true)), bind_tc_ok] using htail
    exact AspisR1.TerminalV4SelectorLoopCanonical.loop_success_canonical
      values mask false AspisR1SelectedMaskProbe.field.QM31.ZERO out hvalues zero_one_canonical.1 hloop
end AspisR1.TerminalV4SelectorMaskSumCanonical
