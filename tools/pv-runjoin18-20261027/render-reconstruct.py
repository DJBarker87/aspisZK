"""One named source reconstruction step per module; consume symbolic parent facts."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
header='''set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Reconstruct18
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_AppendNative17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

'''
for label in ['transfer','withdrawal']:
 for j in reversed(range(21)):
  mod=f'PV_RunJoin_Reconstruct{label.title()}{j:02}18'
  imp='import R1Z.PV_RunJoin_AppendNative17\nimport R1Z.PV_RunJoin_ParentValue17\nimport R1Z.PV_RunJoin_OwnedConstructor18\n'
  if j<20:imp+=f'import R1Z.PV_RunJoin_Reconstruct{label.title()}{j+1:02}18\n'
  state=f'{label}{j}'
  # At level 0, the set bit reads the new frontier leaf; at higher levels read empty.
  node=state if j else 'PV_Src_CanonicalRoots.table.val[0]!'
  if label=='withdrawal' and j==20: imp='import R1Z.PV_RunJoin_ReconstructTransfer0018\n'+imp
  s=imp+header
  s+=f'''theorem {label}_suffix{j} (frontier : PV_RunJoin_ZeroTree17.Frontier)'''+('' if j else f' (hf : frontier.val[0]! = {label}0)')+f''' :
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨{j}#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table {state if j else 'PV_Src_CanonicalRoots.table.val[0]!'} = ok {label}20 := by
  rw [incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop]
'''
  if j==20:s+='  with_unfolding_all rfl\n'
  else:
   s+='  rw [PV_Src_Forest_BankRange.next_some]\n' if False else ''
   s+=f"""  obtain ⟨⟨a,b⟩,hn,hv,he⟩ := PV_Src_Forest_BankRange.next_some (⟨{j}#usize,20#usize⟩ : core.ops.range.Range Usize) (by decide)
  have hs : a = {j+1}#usize := UScalar.eq_of_val_eq hv
  change b = 20#usize at he
  rw [hs,he] at hn
  rw [hn]
  simp only [bind_tc_ok,lift]
  rw [if_{'neg' if j==0 else 'pos'} (by rw [BuilderStdModels.shift64_spec]; decide)]
  rw [index_ok_gen {'frontier' if j==0 else 'PV_Src_CanonicalRoots.table'} {j}#usize (by decide)]
  simp only [bind_tc_ok]
"""

   s+=f'''  change (do
    let p ← format.pool_v1_tree_parent {state if j else 'frontier.val[0]!'} PV_Src_CanonicalRoots.table.val[{j}]!
    incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root_from_level_loop
      ⟨{j+1}#usize,20#usize⟩ 1#u64 frontier PV_Src_CanonicalRoots.table p) = _
'''
   if j==0:s+='  rw [hf]\n'
   s+=f'''  have hp : format.pool_v1_tree_parent {label}{j} PV_Src_CanonicalRoots.table.val[{j}]! = ok {label}{j+1} := by
    apply PV_RunJoin_ParentValue17.source
    · exact PV_Src_CanonicalRoots.canonical ⟨{j},by decide⟩
    · intro k hk; interval_cases k <;> decide
    · exact {label}_node{j}
  rw [hp]
  simp only [bind_tc_ok]
  exact {label}_suffix{j+1} frontier
'''
  s+=f'#print axioms {label}_suffix{j}\nend R1Z.PV_RunJoin_Reconstruct18\n'
  if label=='transfer' and j==20:
   s=(R/'evidence/pv-runjoin18-20261027/51008-PV_RunJoin_ReconstructTransfer2018.lean.txt').read_text()
  target=L/(mod+'.lean')
  if '--check' in sys.argv: assert target.read_text()==s,mod
  else: target.write_text(s)
