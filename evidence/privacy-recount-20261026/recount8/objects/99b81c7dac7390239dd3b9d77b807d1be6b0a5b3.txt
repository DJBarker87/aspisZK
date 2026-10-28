import R1Z.PV_RunJoin_WeightKernel46
import AspisR1ProducerRelease47.CircleFactors49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightLineFactor46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def run (x y : K) : Result (Array K 4#usize) := do
  let q ← PV_B2_C_WeightsNative.aspis_core.field.QM31.mul x y
  ok (Array.make 4#usize [PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE,x,y,q])

theorem complete (x y : K) :
    AspisR1ProducerRelease47.factors.line (toQ x) (toQ y)=
      mapResult (amap toQ) (run x y) := by
  unfold AspisR1ProducerRelease47.factors.line run
  rw [PV_RunJoin_WeightKernel46.one]
  symm
  rw [PV_RunJoin_WeightKernel46.mul]
  apply map_bind toQ (amap toQ)
  intro q
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightLineFactor46
