"""Named single-coordinate source proofs; never unfold the ten-cell recurrence together."""
from pathlib import Path
R=Path(__file__).resolve().parents[2]
for i in range(1,10):
 prev=f'PV_RunJoin_WeightPointsStage{i-1}47';name=f'PV_RunJoin_WeightPointsStage{i}47'
 h='\n    (h7 : Array.index_usize z 7#usize=ok bit7)' if i<7 else ''
 proof=f'''  rw [stage{i},result,PV_RunJoin_WeightSuccessor46.remaining]
  simp only [sub{i+1},cast{i},bind_assoc]
'''
 if i==7:
  proof+='''  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro bit h7
'''
  proof+=f'  simp only [{prev}.complete z _ _ bit h7,result,bind_assoc]\n'
 elif i<7:proof+=f'  simp only [{prev}.complete z _ _ bit7 h7,result,bind_assoc]\n'
 else:proof+=f'  simp only [{prev}.complete,result,bind_assoc]\n'
 s=f'''import R1Z.{prev}
set_option autoImplicit false
namespace R1Z.{name}
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightPointsStages47
open PV_RunJoin_WeightPointsFinish47 (result)
open PV_RunJoin_WeightPointCounters47

theorem complete (z out : Point) (carry bit7 : PV_B2_F_ConstructorCarrier.K){h} :
    stage{i} z out carry bit7=
      result z (PV_RunJoin_WeightSuccessor46.remaining z {i+1} out {i+1}#u8 carry) := by
{proof}#print axioms complete
end R1Z.{name}
'''
 (R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{name}.lean').write_text(s)
