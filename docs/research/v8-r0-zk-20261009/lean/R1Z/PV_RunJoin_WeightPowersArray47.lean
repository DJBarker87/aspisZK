import R1Z.PV_RunJoin_WeightPowersLoop47
import R1Z.PV_RunJoin_WeightCellIndices46
import R1Z.PV_RunJoin_WeightArray46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPowersArray47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)

theorem one : AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE=
    toWide PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ONE := by
  unfold AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE
    PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ONE toWide
  rw [PV_RunJoin_WeightQuartic46.one,PV_RunJoin_WeightQuartic46.zero]
#print axioms one

theorem complete (x : E) : AspisR1ProducerRelease47.kappa (toWide x)=
    mapResult (amap toWide) (PV_B2_251c1.prover_powers.powers 7#usize x) := by
  rw [AspisR1ProducerRelease47.kappa,PV_B2_251c1.prover_powers.powers]
  rw [PV_RunJoin_WeightCellIndices46.zero,one,←PV_RunJoin_WeightArray46.replicate]
  exact PV_RunJoin_WeightPowersLoop47.complete x _ _ 7 0#usize 7#u8 rfl (by decide)
#print axioms complete
end R1Z.PV_RunJoin_WeightPowersArray47
