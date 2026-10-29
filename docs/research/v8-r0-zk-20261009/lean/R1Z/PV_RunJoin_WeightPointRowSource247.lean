import R1Z.PV_RunJoin_WeightPointRowStages47
import R1Z.PV_RunJoin_WeightFactorWriteCps47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowSource247
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors Points row2)
open PV_RunJoin_WeightPointRowStages47
attribute [local irreducible] PV_B2_C_WeightsNative.aspis_core.field.QM31.sub
  PV_B2_C_WeightsNative.aspis_core.field.QM31.mul

theorem complete (fs : Factors) (points : Points) : row2 fs points=(do
    let p ← Array.index_usize points 2#usize
    stage0 p fs 2#usize) := by
  simp only [row2,stage0,stage1,stage2,stage3,stage4,
    PV_RunJoin_WeightPointFactor46.run,PV_RunJoin_WeightFactorWriteCps47.complete,
    bind_assoc,bind_tc_ok]
  simp only [PV_RunJoin_WeightFactorWrite47.write]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRowSource247
