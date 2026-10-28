import R1Z.PV_RunJoin_WeightPowersArray47
import R1Z.PV_RunJoin_WeightArraySeven47
import R1Z.PV_RunJoin_WeightCellSource47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPowersSeven47
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightWide46 (E toWide)
open PV_RunJoin_WeightCellSource47 (Powers powerArray)
open PV_B2_F_ConstructorCarrier (amap)

theorem complete (x : E) : ∃ k : Powers,
    PV_B2_251c1.host_weights.powers7 x=ok k ∧
    AspisR1ProducerRelease47.kappa (toWide x)=ok (amap toWide (powerArray k)) := by
  obtain ⟨a,ha⟩ := PV_B2_C_PowersTotal.source 7#usize x
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,he⟩ := PV_RunJoin_WeightArraySeven47.shape a
  subst a
  refine ⟨(a0,a1,a2,a3,a4,a5,a6),?_,?_⟩
  · simp only [PV_B2_251c1.host_weights.powers7,ha,
      PV_RunJoin_WeightCellIndices46.index0,PV_RunJoin_WeightCellIndices46.index1,
      PV_RunJoin_WeightCellIndices46.index2,PV_RunJoin_WeightCellIndices46.index3,
      PV_RunJoin_WeightCellIndices46.index4,PV_RunJoin_WeightCellIndices46.index5,
      PV_RunJoin_WeightCellIndices46.index6,bind_tc_ok]
  · rw [PV_RunJoin_WeightPowersArray47.complete,ha]
    rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightPowersSeven47
