import R1Z.PV_RunJoin_WeightKernel46
import AspisR1ProducerRelease47.CircleFactors49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightDoubleFactor46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def run (x : K) : Result (K) := do
  let q ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul x x
  let q1 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.add q q
  PV_B2_C_WeightsNative.aspis_core.field.QM31.sub q1 PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE

theorem complete (x : K) :
    AspisR1ProducerRelease47.factors.double (toQ x)=
      mapResult toQ (run x) := by
  unfold AspisR1ProducerRelease47.factors.double run
  rw [PV_RunJoin_WeightKernel46.one]
  symm
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ toQ
  intro q
  rw [PV_RunJoin_WeightKernel46.add]
  apply map_bind toQ toQ
  intro q1
  exact (PV_RunJoin_WeightKernel46.sub q1 _).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightDoubleFactor46
