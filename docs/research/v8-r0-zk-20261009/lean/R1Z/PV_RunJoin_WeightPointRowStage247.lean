import R1Z.PV_RunJoin_WeightPointRowStage347
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowStage247
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightPointRowStages47 (Point stage2 stage3)
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightRowIndices47

theorem complete (p : Point) (fs : Factors) (slot : Usize) (m : Matrix)
    (hr : Array.index_usize fs slot=ok m) (hs : slot.val<5) :
    stage2 p fs slot=(do
      let m1 ← PV_RunJoin_WeightPointRows46.remaining p 3 m 2#usize
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  have tail : ∀ m1 : Matrix, stage3 p (Aeneas.Std.Array.set fs slot m1) slot=(do
      let m2 ← PV_RunJoin_WeightPointRows46.remaining p 2 m1 3#usize
      ok (Aeneas.Std.Array.set fs slot m2)) := by
    intro m1
    rw [PV_RunJoin_WeightPointRowStage347.complete p _ slot m1
      (PV_RunJoin_WeightFactorWrite47.read_set fs slot m1 hs) hs]
    simp only [PV_RunJoin_WeightFactorWrite47.overwrite]
  rw [stage2,PV_RunJoin_WeightPointRows46.remaining]
  simp only [tau2,coord9_2,coord8_2,PV_RunJoin_WeightCounters46.add2,bind_tc_ok,bind_assoc,
    PV_RunJoin_WeightFactorWrite47.equation,hr,tail]
#print axioms complete
end R1Z.PV_RunJoin_WeightPointRowStage247
