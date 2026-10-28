import R1Z.PV_RunJoin_WeightPointRowStages47
import R1Z.PV_RunJoin_WeightRowIndices47
import R1Z.PV_RunJoin_WeightFactorRestore47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowStage447
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightPointRowStages47 (Point stage4)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightRowIndices47

theorem complete (p : Point) (fs : Factors) (slot : Usize) (m : Matrix)
    (hr : Array.index_usize fs slot=ok m) (hs : slot.val<5) :
    stage4 p fs slot=(do
      let m1 ← PV_RunJoin_WeightPointRows46.remaining p 1 m 4#usize
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  rw [stage4,PV_RunJoin_WeightPointRows46.remaining]
  simp only [tau4,coord9_4,coord8_4,bind_tc_ok,bind_assoc,
    PV_RunJoin_WeightFactorWrite47.equation,hr,
    PV_RunJoin_WeightPointRows46.remaining]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRowStage447
