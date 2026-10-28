import R1Z.PV_RunJoin_WeightKernel46
import AspisR1ProducerRelease47.CircleFactors49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointFactor46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def run (a b : K) : Result (Array K 4#usize) := do
  let q ← PV_B2_C_WeightsNative.aspis_core.field.QM31.sub PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE a
  let q1 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.sub PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE b
  let q2 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul q q1
  let q3 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul a q1
  let q4 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul q b
  let q5 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul a b
  ok (Array.make 4#usize [q2,q3,q4,q5])

theorem complete (a b : K) :
    AspisR1ProducerRelease47.factors.point (toQ a) (toQ b)=
      mapResult (amap toQ) (run a b) := by
  unfold AspisR1ProducerRelease47.factors.point run
  rw [PV_RunJoin_WeightKernel46.one]
  symm
  rw [PV_RunJoin_WeightKernel46.sub]
  apply map_bind toQ (amap toQ)
  intro q
  rw [PV_RunJoin_WeightKernel46.sub]
  apply map_bind toQ (amap toQ)
  intro q1
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ (amap toQ)
  intro q2
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ (amap toQ)
  intro q3
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ (amap toQ)
  intro q4
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ (amap toQ)
  intro q5
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightPointFactor46
