from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
s='\n'.join(p.read_text() for p in sorted((R/'lean').glob('JGh_TX2_Frontier*.lean')))
for tree,last,model in [(0,185,'JGf_TX2_M0Roots'),(2,163,'JGc_TX2_M2Roots')]:
 ns=f'JGk_TX2_FrontierOrder{tree}'
 coords=[f'JGh_TX2_Frontiers.coords{tree}_{i:03}' for i in range(last+1)]
 streams=[f'JGk_TX2_Group{tree}_{i:02}.stream' for i in range(18)]
 groups=[f'JGk_TX2_Group{tree}_{i:02}.group' for i in range(18)]
 body=f'''import JGk_TX2_Group{tree}_00
import JGh_TX2_FrontierHeight17
import Mathlib.Data.Multiset.AddSub
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open JGk_TX2_OrderTools

theorem permutation : JGh_TX2_Frontiers.coords{tree}_{last:03}.Perm JGk_TX2_Group{tree}_00.stream := by
  apply Multiset.coe_eq_coe.mp
  simp only [{','.join(coords+streams+groups)},←Multiset.coe_add,
    ←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero,zero_add]
  ac_rfl
#print axioms permutation

theorem source : OraclePortSelectedDraft.orderedFrontier {model}.indices=JGk_TX2_Group{tree}_00.stream := by
  rw [OraclePortSelectedDraft.orderedFrontier,JGh_TX2_Frontiers.front{tree}_{last:03}]
  trans JGh_TX2_Frontiers.coords{tree}_{last:03}.mergeSort (fun a b => decide (le a b))
  · apply congrArg (fun cmp => JGh_TX2_Frontiers.coords{tree}_{last:03}.mergeSort cmp)
    funext a b
    exact decide_eq_decide.mpr Iff.rfl
  · exact sorted_permutation _ _ permutation JGk_TX2_Group{tree}_00.stream_ordered
#print axioms source
end AspisR1.{ns}
end
'''
 (R/'lean'/f'{ns}.lean').write_text(body)
