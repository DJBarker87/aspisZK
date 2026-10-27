#!/usr/bin/env python3
"""Emit source-cell consumers of symbolic parent refinement and pinned model cells."""
from pathlib import Path
import sys,json,hashlib
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';check='--check' in sys.argv
rows=[]
for i in range(21):
 m=f'PV_Src_RootCell{i:02d}'
 lhs='PV_Src_RootZero.zero' if i==0 else f'PV_Src_CanonicalRoots.table.val[{i-1}]!'
 rhs=f'PV_Src_CanonicalRoots.table.val[{i}]!'
 proof='''  apply PV_Src_PortParent.source
  · exact PV_Src_RootZero.canonical 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩
  · rw [PV_Src_RootZero.meaning,PV_Src_RootFieldMeaning.source ⟨0,by decide⟩]
    exact PV_RunJoin_RootModel.initial''' if i==0 else f'''  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨{i-1},by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨{i},by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨{i-1},by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨{i},by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨{i-1},by decide⟩'''
 text=f'''import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.{m}
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell {i}; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    {lhs} {lhs} = ok {rhs} := by
{proof}

#print axioms source
end R1Z.{m}
'''
 p=b/(m+'.lean')
 if check:assert p.read_text()==text,m
 else:p.write_text(text)
 assert not any(t in text for t in ['norm_num','native_decide','unfold','simp '])
 rows.append(dict(cell=i,module='R1Z.'+m,sha256=hashlib.sha256(text.encode()).hexdigest(),proof_shape='zero digest' if i==0 else 'adjacent frozen parents',symbolic_parent='PV_Src_PortParent.source',mathematical_cell='PV_RunJoin_RootModel.initial' if i==0 else 'PV_RunJoin_RootModel.parents'))
(root/'evidence/pv-srcid3-20261026/resume9-cell-preflight.json').write_text(json.dumps(dict(check_passed=check,cells=rows),indent=2)+'\n')
print('21 symbolic source-cell consumers match generator' if check else 'emitted 21 consumers')
