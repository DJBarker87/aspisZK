"""Small independent ordering certificates over the frozen reference blocks."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2]; lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
outputs={}
for i in range(60):
 name=f'PV_CBM_CellChunk{i:02}'
 source=(lean/(name+'.lean')).read_text()
 rows=[(int(r),int(c)) for r,c in re.findall(r'\{row := (\d+)#u16, column := (\d+)#u8\}',source.split('def literals :')[1].split('theorem length')[0])]
 assert rows and all(1024*c+r<1024*d+s for (r,c),(s,d) in zip(rows,rows[1:]))
 lo=1024*rows[0][1]+rows[0][0];hi=1024*rows[-1][1]+rows[-1][0]
 mod=f'PV_Op134_CellOrder{i:02}'
 outputs[mod]=f'''import R1Z.{name}
import R1Z.PV_Op134_Order
namespace R1Z.{mod}
open PV_Op134_Order
set_option autoImplicit false
theorem sorted : increasing {name}.literals := by
  unfold increasing
  decide
-- Small literal block checks; no recurrence or finite-field arithmetic unfolds.
theorem bounds : ∀ c ∈ {name}.literals,
    {lo} ≤ key c ∧ key c ≤ {hi} ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
  simp only [{name}.literals, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  intro c h
  rcases h with { ' | '.join('h' for _ in rows) } <;> subst c <;> decide
#print axioms sorted
#print axioms bounds
end R1Z.{mod}
'''
check='--check' in sys.argv
for n,s in outputs.items():
 p=lean/(n+'.lean')
 if check:assert p.read_text()==s,n
 else:p.write_text(s)
print('CHECK' if check else 'GENERATED',len(outputs),'ordering blocks')
