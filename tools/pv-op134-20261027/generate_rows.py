"""Rows split into small blocks, taken verbatim from the published extraction."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(lean/'PV_CBM_RowsReference.lean').read_text();rows=list(map(int,re.findall(r'Vec.push \w+ (\d+)#u16',s)))
assert len(rows)==214 and rows==sorted(set(rows))
outputs={}
for i in range(14):
 rs=rows[16*i:16*(i+1)];mod=f'PV_Op134_Rows{i:02}'
 outputs[mod]=f'''import R1Z.PV_CBM_PushList
namespace R1Z.{mod}
open Aeneas Aeneas.Std Result
set_option autoImplicit false
def rows : List U16 := [{', '.join(str(r)+'#u16' for r in rs)}]
theorem sorted : rows.Pairwise (fun a b => a.val < b.val) := by decide
theorem bounds : ∀ r ∈ rows, {rs[0]} ≤ r.val ∧ r.val ≤ {rs[-1]} ∧ r.val < 1024 := by
  simp only [rows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro r h
  rcases h with {' | '.join('h' for _ in rs)} <;> subst r <;> decide
theorem length : rows.length = {len(rs)} := rfl
#print axioms sorted
#print axioms bounds
#print axioms length
end R1Z.{mod}
'''
check='--check' in sys.argv
for n,s in outputs.items():
 p=lean/(n+'.lean')
 if check:assert p.read_text()==s,n
 else:p.write_text(s)
print('CHECK' if check else 'GENERATED',len(outputs),'row blocks')
