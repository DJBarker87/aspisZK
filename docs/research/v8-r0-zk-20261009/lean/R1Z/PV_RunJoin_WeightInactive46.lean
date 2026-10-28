import R1Z.PV_RunJoin_WeightRow46
import R1Z.PV_RunJoin_WeightQuartic46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightInactive46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightMap46 (mapResult)

-- Only the fixed 64-word mask table is compared. No 1024-row run is reduced.
theorem masks : PV_B2_251c1.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS=
    AspisR1InactiveOwner49.owned.MASKS := by
  unfold PV_B2_251c1.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS
    AspisR1InactiveOwner49.owned.MASKS
  rfl

theorem complete (w : W) (hs : w.variant=.S2) (j : Usize) :
    ProverCommitInactiveOutput49.run j=
      mapResult toQ (PV_B2_251c1.host_weights.raw_value w 0#usize j) := by
  simp only [PV_B2_251c1.host_weights.raw_value,if_true,hs,
    PV_RunJoin_WeightRow46.row,masks,ProverCommitInactiveOutput49.run,
    AspisR1InactiveOwner49.owned.inactive]
  obtain ⟨r,hr,_⟩ := ProverCommitInactiveRow49.row_exact j
  rw [hr]
  simp only [bind_tc_ok]
  cases hd : r / 16#usize with
  | fail e => simp only [hd,mapResult,bind_tc_fail]
  | div => simp only [hd,mapResult,bind_tc_div]
  | ok d =>
    simp only [hd,bind_tc_ok]
    cases hm : Array.index_usize AspisR1InactiveOwner49.owned.MASKS d with
    | fail e => simp only [hm,mapResult,bind_tc_fail]
    | div => simp only [hm,mapResult,bind_tc_div]
    | ok m =>
      simp only [hm,bind_tc_ok]
      cases hb : r % 16#usize with
      | fail e => simp only [hb,mapResult,bind_tc_fail]
      | div => simp only [hb,mapResult,bind_tc_div]
      | ok b =>
        simp only [hb,lift,bind_tc_ok]
        split <;> simp only [mapResult,PV_RunJoin_WeightQuartic46.one,
          PV_RunJoin_WeightQuartic46.zero]
#print axioms masks
#print axioms complete
end R1Z.PV_RunJoin_WeightInactive46
