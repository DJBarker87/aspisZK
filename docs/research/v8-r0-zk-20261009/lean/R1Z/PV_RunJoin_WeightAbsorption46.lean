import R1Z.PV_RunJoin_WeightSuccessor46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightAbsorption46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K amap)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def run (p : Array K 10#usize) : Result (Array K 10#usize) := do
  let q ← Array.index_usize p 7#usize
  let q1 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.sub
    PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE q
  let p1 ← Array.update p 7#usize q1
  let q2 ← Array.index_usize p1 6#usize
  let q3 ← PV_B2_C_WeightsNative.aspis_core.field.QM31.sub
    PV_B2_C_WeightsNative.aspis_core.field.QM31.ONE q2
  Array.update p1 6#usize q3

theorem complete (p : Array K 10#usize) :
    AspisR1ProducerRelease47.points.absorption (amap toQ p)=
      mapResult (amap toQ) (run p) := by
  unfold AspisR1ProducerRelease47.points.absorption run
  rw [PV_RunJoin_WeightMap46.index]
  symm
  apply map_bind toQ (amap toQ)
  intro q
  rw [PV_RunJoin_WeightKernel46.sub]
  apply map_bind toQ (amap toQ)
  intro q1
  rw [PV_RunJoin_WeightUpdate46.complete]
  apply map_bind (amap toQ) (amap toQ)
  intro p1
  rw [PV_RunJoin_WeightMap46.index]
  apply map_bind toQ (amap toQ)
  intro q2
  rw [PV_RunJoin_WeightKernel46.sub]
  apply map_bind toQ (amap toQ)
  intro q3
  exact (PV_RunJoin_WeightUpdate46.complete toQ p1 6#usize q3).symm
#print axioms complete
end R1Z.PV_RunJoin_WeightAbsorption46
