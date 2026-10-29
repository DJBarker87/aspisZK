import R1Z.PV_RunJoin_WeightPointRowStage147
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowStage047
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightPointRowStages47 (Point stage0 stage1)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightRowIndices47

theorem complete (p : Point) (fs : Factors) (slot : Usize) (m : Matrix)
    (hr : Array.index_usize fs slot=ok m) (hs : slot.val<5) :
    stage0 p fs slot=(do
      let m1 ← PV_RunJoin_WeightPointRows46.remaining p 5 m 0#usize
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  have tail : ∀ m1 : Matrix, stage1 p (Aeneas.Std.Array.set fs slot m1) slot=(do
      let m2 ← PV_RunJoin_WeightPointRows46.remaining p 4 m1 1#usize
      ok (Aeneas.Std.Array.set fs slot m2)) := by
    intro m1
    rw [PV_RunJoin_WeightPointRowStage147.complete p _ slot m1
      (PV_RunJoin_WeightFactorWrite47.read_set fs slot m1 hs) hs]
    simp only [PV_RunJoin_WeightFactorWrite47.overwrite]
  rw [stage0,PV_RunJoin_WeightPointRows46.remaining]
  simp only [tau0,coord9_0,coord8_0,PV_RunJoin_WeightCounters46.add0,bind_tc_ok,bind_assoc,
    PV_RunJoin_WeightFactorWrite47.equation,hr,tail]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRowStage047
