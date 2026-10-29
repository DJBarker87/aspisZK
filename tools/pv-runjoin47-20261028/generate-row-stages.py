"""Aggregate point-row restoration one checked factor cell at a time."""
from pathlib import Path
R=Path(__file__).resolve().parents[2]
for d in range(3,-1,-1):
 name=f'PV_RunJoin_WeightPointRowStage{d}47';prev=f'PV_RunJoin_WeightPointRowStage{d+1}47'
 inc=f'PV_RunJoin_WeightCounters46.add{d}'
 s=f'''import R1Z.{prev}
set_option autoImplicit false
namespace R1Z.{name}
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightPointRowStages47 (Point stage{d} stage{d+1})
open PV_RunJoin_WeightFactorWrite47 (Matrix)
open PV_RunJoin_WeightRowIndices47

theorem complete (p : Point) (fs : Factors) (slot : Usize) (m : Matrix)
    (hr : Array.index_usize fs slot=ok m) (hs : slot.val<5) :
    stage{d} p fs slot=(do
      let m1 ← PV_RunJoin_WeightPointRows46.remaining p {5-d} m {d}#usize
      ok (Aeneas.Std.Array.set fs slot m1)) := by
  have tail : ∀ m1 : Matrix, stage{d+1} p (Aeneas.Std.Array.set fs slot m1) slot=(do
      let m2 ← PV_RunJoin_WeightPointRows46.remaining p {4-d} m1 {d+1}#usize
      ok (Aeneas.Std.Array.set fs slot m2)) := by
    intro m1
    rw [{prev}.complete p _ slot m1
      (PV_RunJoin_WeightFactorWrite47.read_set fs slot m1 hs) hs]
    simp only [PV_RunJoin_WeightFactorWrite47.overwrite]
  rw [stage{d},PV_RunJoin_WeightPointRows46.remaining]
  simp only [tau{d},coord9_{d},coord8_{d},{inc},bind_tc_ok,bind_assoc,
    PV_RunJoin_WeightFactorWrite47.equation,hr,tail]
#print axioms complete
end R1Z.{name}
'''
 (R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{name}.lean').write_text(s)
