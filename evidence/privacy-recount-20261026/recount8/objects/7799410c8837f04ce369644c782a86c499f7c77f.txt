import R1Z.PV_RunJoin_WeightRows46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRowArray46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult map_bind)

def run (w : W) (j : Usize) : Result (Array Q 7#usize) := do
  let q0 ← PV_B2_251c1.host_weights.raw_value w 0#usize j
  let q1 ← PV_B2_251c1.host_weights.raw_value w 1#usize j
  let q2 ← PV_B2_251c1.host_weights.raw_value w 2#usize j
  let q3 ← PV_B2_251c1.host_weights.raw_value w 3#usize j
  let q4 ← PV_B2_251c1.host_weights.raw_value w 4#usize j
  let q5 ← PV_B2_251c1.host_weights.raw_value w 5#usize j
  let q6 ← PV_B2_251c1.host_weights.raw_value w 6#usize j
  ok (Array.make 7#usize [q0,q1,q2,q3,q4,q5,q6])

theorem complete (w : W) (hs : w.variant=.S2) (j : Usize) :
    AspisR1ProducerRelease47.weights53.row (state w) j=mapResult (amap toQ) (run w j) := by
  unfold AspisR1ProducerRelease47.weights53.row run
  symm
  rw [PV_RunJoin_WeightRows46.raw w hs 0#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q0
  rw [PV_RunJoin_WeightRows46.raw w hs 1#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q1
  rw [PV_RunJoin_WeightRows46.raw w hs 2#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q2
  rw [PV_RunJoin_WeightRows46.raw w hs 3#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q3
  rw [PV_RunJoin_WeightRows46.raw w hs 4#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q4
  rw [PV_RunJoin_WeightRows46.raw w hs 5#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q5
  rw [PV_RunJoin_WeightRows46.raw w hs 6#usize j (by decide)]
  apply map_bind toQ (amap toQ)
  intro q6
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightRowArray46
