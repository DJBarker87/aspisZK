import R1Z.PV_RunJoin_WeightConstructorRows47
import R1Z.PV_RunJoin_WeightPoints47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightConstructorModelRows47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K Point amap)
open PV_B2_C_ConstructorRows (Points)
open PV_RunJoin_WeightKernel46 (toQ)
open PV_RunJoin_WeightMap46 (mapResult map_bind)
abbrev MF := Array (Array (Array PV_RunJoin_WeightCarrier46.MQ 4#usize) 5#usize) 5#usize

def run (p : Points) (z : Array Point 2#usize) : Result MF := do
  let p0 ← Array.index_usize (amap (amap toQ) p) 0#usize
  let r0 ← AspisR1ProducerRelease47.point_rows.all p0
  let p1 ← Array.index_usize (amap (amap toQ) p) 1#usize
  let r1 ← AspisR1ProducerRelease47.point_rows.all p1
  let p2 ← Array.index_usize (amap (amap toQ) p) 2#usize
  let r2 ← AspisR1ProducerRelease47.point_rows.all p2
  let z0 ← Array.index_usize z 0#usize
  let r3 ← AspisR1ProducerRelease47.factors.circle_rows (toQ z0.x) (toQ z0.y)
  let z1 ← Array.index_usize z 1#usize
  let r4 ← AspisR1ProducerRelease47.factors.circle_rows (toQ z1.x) (toQ z1.y)
  ok (Array.make 5#usize [r0,r1,r2,r3,r4])

theorem complete (p : Points) (z : Array Point 2#usize) : run p z=
    mapResult (amap (amap (amap toQ))) (PV_RunJoin_WeightConstructorRows47.run p z) := by
  unfold run PV_RunJoin_WeightConstructorRows47.run
  symm
  rw [PV_RunJoin_WeightMap46.index]
  apply map_bind (amap toQ) (amap (amap (amap toQ)))
  intro p0
  rw [PV_RunJoin_WeightPointRows47.model]
  apply map_bind (amap (amap toQ)) (amap (amap (amap toQ)))
  intro r0
  rw [PV_RunJoin_WeightMap46.index]
  apply map_bind (amap toQ) (amap (amap (amap toQ)))
  intro p1
  rw [PV_RunJoin_WeightPointRows47.model]
  apply map_bind (amap (amap toQ)) (amap (amap (amap toQ)))
  intro r1
  rw [PV_RunJoin_WeightMap46.index]
  apply map_bind (amap toQ) (amap (amap (amap toQ)))
  intro p2
  rw [PV_RunJoin_WeightPointRows47.model]
  apply map_bind (amap (amap toQ)) (amap (amap (amap toQ)))
  intro r2
  rw [PV_RunJoin_WeightResult46.shared_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro z0 _
  rw [PV_RunJoin_WeightCircleRows47.model]
  apply map_bind (amap (amap toQ)) (amap (amap (amap toQ)))
  intro r3
  rw [PV_RunJoin_WeightResult46.shared_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro z1 _
  rw [PV_RunJoin_WeightCircleRows47.model]
  apply map_bind (amap (amap toQ)) (amap (amap (amap toQ)))
  intro r4
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightConstructorModelRows47
