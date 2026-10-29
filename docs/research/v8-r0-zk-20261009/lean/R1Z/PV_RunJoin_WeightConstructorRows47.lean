import R1Z.PV_RunJoin_WeightPointRowSource047
import R1Z.PV_RunJoin_WeightPointRowSource147
import R1Z.PV_RunJoin_WeightPointRowSource247
import R1Z.PV_RunJoin_WeightCircleRows47
import R1Z.PV_RunJoin_WeightFiveSet47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightConstructorRows47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K Point)
open PV_B2_C_ConstructorRows (Factors Points)

def run (p : Points) (z : Array Point 2#usize) : Result Factors := do
  let p0 ← Array.index_usize p 0#usize
  let r0 ← PV_RunJoin_WeightPointRows47.run p0
  let p1 ← Array.index_usize p 1#usize
  let r1 ← PV_RunJoin_WeightPointRows47.run p1
  let p2 ← Array.index_usize p 2#usize
  let r2 ← PV_RunJoin_WeightPointRows47.run p2
  let z0 ← Array.index_usize z 0#usize
  let r3 ← PV_RunJoin_WeightCircleRows47.run z0.x z0.y
  let z1 ← Array.index_usize z 1#usize
  let r4 ← PV_RunJoin_WeightCircleRows47.run z1.x z1.y
  ok (Array.make 5#usize [r0,r1,r2,r3,r4])

theorem complete (p : Points) (z : Array Point 2#usize) (fs : Factors) :
    PV_RunJoin_WeightConstructorThread46.rows p z fs=run p z := by
  have h0 (a : Array K 10#usize) (f : Factors) := PV_RunJoin_WeightPointRows47.source a f 0#usize (by decide)
  have h1 (a : Array K 10#usize) (f : Factors) := PV_RunJoin_WeightPointRows47.source a f 1#usize (by decide)
  have h2 (a : Array K 10#usize) (f : Factors) := PV_RunJoin_WeightPointRows47.source a f 2#usize (by decide)
  have h3 (f : Factors) (x y : K) := PV_RunJoin_WeightCircleRows47.source f 3#usize x y (by decide)
  have h4 (f : Factors) (x y : K) := PV_RunJoin_WeightCircleRows47.source f 4#usize x y (by decide)
  simp only [PV_RunJoin_WeightConstructorThread46.rows,
    PV_RunJoin_WeightPointRowSource047.complete,PV_RunJoin_WeightPointRowSource147.complete,
    PV_RunJoin_WeightPointRowSource247.complete,PV_RunJoin_WeightCircleSource47.row3,
    PV_RunJoin_WeightCircleSource47.row4,h0,h1,h2,h3,h4,run,bind_assoc,bind_tc_ok,
    PV_RunJoin_WeightFiveSet47.complete]
#print axioms complete
end R1Z.PV_RunJoin_WeightConstructorRows47
