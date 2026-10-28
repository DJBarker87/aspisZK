import R1Z.PV_RunJoin_WeightNormalize46
import R1Z.PV_RunJoin_WeightWide46
import AspisR1ProducerRelease47.Weights49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightScale46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E toWide)
open PV_RunJoin_WeightMap46 (mapResult)

theorem canonical (q : Q) :
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31 (toQ q)=
      ok (toQ (PV_B2_D_MulQm31Total.V.norm q)) := by
  simp only [AspisR1ProducerRelease47.field.wide_exact.canonical_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    toQ,PV_B2_D_MulQm31Total.V.norm,PV_RunJoin_WeightNormalize46.complete,bind_tc_ok]

theorem complete (x : E) (q : Q) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_qm31 (toWide x) (toQ q)=
      mapResult toWide (PV_B2_251c1.host_weights.mul_qm31 x q) := by
  rw [PV_B2_D_MulQm31Total.source]
  simp only [AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_qm31,
    canonical,toWide,PV_B2_D_MulQm31Total.V.value,
    PV_RunJoin_WeightQuartic46.mul_value,bind_tc_ok,mapResult,
    PV_B2_E_OrdinaryOriginal.mapResult]
#print axioms canonical
#print axioms complete
end R1Z.PV_RunJoin_WeightScale46
