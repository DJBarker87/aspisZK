import R1Z.PV_RunJoin_WeightCellSource47
import R1Z.PV_RunJoin_WeightFill46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightMutation47
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E)
open PV_RunJoin_WeightCellSource47 (Powers powerArray)
open PV_B2_F_ArrayMutation (ZeroSuffix)
abbrev Out := PV_B2_C_MutationStep.Out

theorem read_zero (out : Out) (j : Usize) (hj : j.val<1024)
    (hz : ZeroSuffix out j.val) :
    Array.index_usize out j=ok PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO := by
  unfold Array.index_usize
  have h := hz j.val (by omega) hj
  change out[j]?=some PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO at h
  rw [h]
#print axioms read_zero

theorem remaining (w : W) (hs : w.variant=.S2) (k : Powers) (n : Nat)
    (out : Out) (j : Usize) (hb : j.val+n≤1024) (hz : ZeroSuffix out j.val) :
    PV_RunJoin_WeightFill46.finite w (powerArray k) n out j=
      PV_B2_F_MutationModel.remaining w k n j out := by
  induction n generalizing out j with
  | zero => rfl
  | succ n ih =>
    have hj : j.val<1024 := by omega
    have hv : (Usize.wrapping_add j 1#usize).val=j.val+1 :=
      PV_B2_C_MutationTotal.next_val j (by scalar_tac)
    obtain ⟨row,hr,_,hc,_⟩ := PV_RunJoin_WeightCellSource47.complete w hs k j hj
    rw [PV_RunJoin_WeightFill46.finite,PV_B2_F_MutationModel.remaining]
    simp only [hr,bind_tc_ok,read_zero out j hj hz]
    rw [←hc,←PV_B2_F_CellFold.source]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro out1 hu
    exact ih out1 _ (by rw [hv];omega) (by
      rw [hv]
      exact PV_B2_F_ArrayMutation.suffix_step out out1 j x hz hu)
#print axioms remaining
end R1Z.PV_RunJoin_WeightMutation47
