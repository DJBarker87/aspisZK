import AspisR1.PoseidonExternalLoopFuel
import AspisR1.PoseidonExternalGroupBlockCanonical
import AspisR1.PoseidonFullRoundCellStep
import PoseidonExternalLoopStep
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoopCanonical
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLoopStep
open AspisR1.PoseidonExternalGroupBlockCanonical
open AspisR1.PoseidonFullRoundCellStep
abbrev State := Array field.QM31 16#usize

theorem loop0_success_canonical_fuel (current : State) (group : Usize) (fuel : Nat)
    (hspan : group.val + fuel = 4) (hcanonical : CanonicalState current) :
    ∃ out : State,
      state_only_poseidon.external_linear_lazy_loop0 current group = .ok out ∧
      CanonicalState out := by
  induction fuel generalizing current group with
  | zero =>
      have hgroup : group.val = 4 := by omega
      have hstop : ¬ group < 4#usize := by scalar_tac
      exact ⟨current, by rw [state_only_poseidon.external_linear_lazy_loop0.eq_def, if_neg hstop], hcanonical⟩
  | succ fuel ih =>
      have hgroup : group.val < 4 := by omega
      obtain ⟨out,group1,hstep,hinc,_⟩ := loop0_step current group hgroup
      obtain ⟨blockOut,hblock,hblockCan⟩ :=
        AspisR1.PoseidonExternalGroupBlockCanonical.group_block_canonical current group hgroup hcanonical
      have hplusSpec : (group + 1#usize : Result Usize) ⦃z => z.val = group.val + 1⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨z,hplus,hplusval⟩ := WP.spec_imp_exists hplusSpec
      have hz : z = group1 := by apply UScalar.eq_of_val_eq; omega
      subst z
      have hspan' : group1.val + fuel = 4 := by rw [hinc]; omega
      obtain ⟨final,hrec,hfinalCan⟩ := ih blockOut group1 hspan' hblockCan
      refine ⟨final, ?_, hfinalCan⟩
      have hstep' := hstep
      simp only [hblock, hplus, bind_tc_ok] at hstep'
      rw [hstep']
      exact hrec

#print axioms loop0_success_canonical_fuel
end AspisR1.PoseidonExternalLoopCanonical
