import PoseidonExternalLoopStep
import PoseidonExternalGroupBlockFrame
import PoseidonExternalGroupUpdateCells
import AspisR1.PoseidonGroupSliceModel
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoopFuel
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLoopStep
open AspisR1.PoseidonExternalGroupBlockFrame
open AspisR1.PoseidonExternalGroupUpdateCells
open AspisR1.PoseidonGroupSliceModel
abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def groupModel (original current : State) (limit : Nat) : Prop :=
  ∀ g : Fin 4, ∀ j : Fin 4,
    if g.val < limit then
      Decode (cellAt current (4 * g.val + j.val)) =
        R0P.poseidonMat4 (fun k => Decode (cell16 original g k)) j
    else
      Decode (cellAt current (4 * g.val + j.val)) =
        Decode (cellAt original (4 * g.val + j.val))

private theorem cell16_eq_cellAt (a : State) (g j : Fin 4) :
    cell16 a g j = cellAt a (4 * g.val + j.val) := by
  have hidx : 4 * g.val + j.val < 16 := by have := g.isLt; have := j.isLt; omega
  simp [cell16, cellAt, hidx]

theorem loop0_success_fuel (original current : State) (group : Usize) (fuel : Nat)
    (hspan : group.val + fuel = 4)
    (hinvariant : groupModel original current group.val) :
    ∃ out : State,
      state_only_poseidon.external_linear_lazy_loop0 current group = .ok out ∧
      groupModel original out 4 := by
  induction fuel generalizing current group with
  | zero =>
      have hgroup : group.val = 4 := by omega
      have hstop : ¬ group < 4#usize := by scalar_tac
      refine ⟨current, ?_, ?_⟩
      · rw [state_only_poseidon.external_linear_lazy_loop0.eq_def, if_neg hstop]
      · intro g j
        simpa [groupModel, hgroup] using hinvariant g j
  | succ fuel ih =>
      have hgroup : group.val < 4 := by omega
      obtain ⟨out, group1, hstep, hinc, _⟩ := loop0_step current group hgroup
      obtain ⟨outBlock, hblock, hframe⟩ :=
        AspisR1.PoseidonExternalGroupBlockFrame.group_block_frame current group hgroup
      obtain ⟨outBody, hbody, hbodyModel⟩ :=
        AspisR1.PoseidonExternalLoopGroupBody.group_body_success current group hgroup
      have hblockBody : groupBlock current group = .ok outBody := by
        simpa only [groupBlock] using hbody
      have houts : outBody = outBlock := Result.ok.inj (hblockBody.symm.trans hblock)
      have hplusSpec : (group + 1#usize : Result Usize) ⦃z => z.val = group.val + 1⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨z,hplus,hplusval⟩ := WP.spec_imp_exists hplusSpec
      have hz : z = group1 := by apply UScalar.eq_of_val_eq; omega
      subst z
      have hspan' : group1.val + fuel = 4 := by rw [hinc]; omega
      have hinvBlock : groupModel original outBlock group1.val := by
        intro g j
        by_cases heq : g.val = group.val
        · have hgEq : g = (⟨group.val,hgroup⟩ : Fin 4) := Fin.ext heq
          subst g
          have hnot : ¬ group.val < group.val := by omega
          have hin : ∀ k : Fin 4, Decode (cell16 current ⟨group.val,hgroup⟩ k) =
              Decode (cell16 original ⟨group.val,hgroup⟩ k) := by
            intro k
            have hc := hinvariant (⟨group.val,hgroup⟩ : Fin 4) k
            rw [if_neg hnot] at hc
            change Decode (cellAt current (4 * group.val + k.val)) =
              Decode (cellAt original (4 * group.val + k.val)) at hc
            simpa only [cell16_eq_cellAt] using hc
          have hm := hbodyModel j
          rw [houts] at hm
          have hfun : (fun k => Decode (cell16 current ⟨group.val,hgroup⟩ k)) =
              (fun k => Decode (cell16 original ⟨group.val,hgroup⟩ k)) := by
            funext k
            exact hin k
          rw [hfun] at hm
          simpa [groupModel, heq, hinc, hgroup] using hm
        · have hidxLt : 4 * g.val + j.val < 16 := by have := g.isLt; have := j.isLt; omega
          let ix : Fin 16 := ⟨4 * g.val + j.val, hidxLt⟩
          have hnotFrame : ∀ r : Fin 4, ix.val ≠ 4 * group.val + r.val := by
            intro r
            have hr := r.isLt
            simp [ix]
            omega
          have hfr := hframe ix hnotFrame
          have hdecodeFrame : Decode (cellAt outBlock ix.val) = Decode (cellAt current ix.val) :=
            congrArg Decode hfr
          have hprev := hinvariant g j
          by_cases hproc : g.val < group.val
          · rw [if_pos hproc] at hprev
            have hltNext : g.val < group1.val := by rw [hinc]; omega
            simp only [groupModel, if_pos hltNext]
            simpa [ix] using hdecodeFrame.trans hprev
          · have hfuture : group.val < g.val := by omega
            rw [if_neg hproc] at hprev
            have hgeNext : ¬ g.val < group1.val := by rw [hinc]; omega
            simp only [groupModel, if_neg hgeNext]
            simpa [ix] using hdecodeFrame.trans hprev
      obtain ⟨final,hrec,hmodel⟩ := ih outBlock group1 hspan' hinvBlock
      refine ⟨final, ?_, hmodel⟩
      have hrun : state_only_poseidon.external_linear_lazy_loop0 current group =
          state_only_poseidon.external_linear_lazy_loop0 outBlock group1 := by
        rw [hstep]
        simp only [hblock, hplus, bind_tc_ok]
      rw [hrun]
      exact hrec

theorem loop0_all_groups (state : State) :
    ∃ out : State,
      state_only_poseidon.external_linear_lazy_loop0 state 0#usize = .ok out ∧
      ∀ g : Fin 4, ∀ j : Fin 4,
        Decode (cellAt out (4 * g.val + j.val)) =
          R0P.poseidonMat4 (fun k => Decode (cell16 state g k)) j := by
  have hinv : groupModel state state 0 := by
    intro g j
    simp [groupModel]
  obtain ⟨out,hrun,hmodel⟩ := loop0_success_fuel state state 0#usize 4 (by decide) hinv
  refine ⟨out,hrun,?_⟩
  intro g j
  simpa [groupModel] using hmodel g j

#print axioms loop0_success_fuel
#print axioms loop0_all_groups
end AspisR1.PoseidonExternalLoopFuel
