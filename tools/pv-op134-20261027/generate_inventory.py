"""Symbolic concatenation: literal blocks remain irreducible in this proof."""
from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2]; lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=''.join(f'import R1Z.PV_Op134_CellOrder{i:02}\n' for i in range(60))
s+='import R1Z.PV_CBM_CellsSpec\nimport R1Z.PV_Op134_Coverage\nnamespace R1Z.PV_Op134_Inventory\nopen PV_Op134_Order\nset_option autoImplicit false\n'
s+='attribute [local irreducible] '+' '.join(f'PV_CBM_CellChunk{i:02}.literals' for i in range(60))+'\n'
bounds=[]
for i in range(60):
 t=(lean/f'PV_CBM_CellChunk{i:02}.lean').read_text().split('def literals :')[1].split('theorem length')[0]
 rs=[(int(r),int(c)) for r,c in re.findall(r'\{row := (\d+)#u16, column := (\d+)#u8\}',t)]
 bounds.append((1024*rs[0][1]+rs[0][0],1024*rs[-1][1]+rs[-1][0]))
s+='theorem ordered_bounds : increasing PV_CBM_CellsSpec.literals ∧\n    ∀ c ∈ PV_CBM_CellsSpec.literals, 13 ≤ key c ∧ key c < 16384 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by\n'
for i in range(60):
 lo,hi=bounds[i];nxt=bounds[i+1][0] if i<59 else 16384
 s+=f'  have b{i} : increasing PV_CBM_CellChunk{i:02}.literals ∧ ∀ c ∈ PV_CBM_CellChunk{i:02}.literals, {lo} ≤ key c ∧ key c < {nxt} ∧ c.row.val < 1024 ∧ c.column.val < 16 := by\n'
 s+=f'    refine ⟨PV_Op134_CellOrder{i:02}.sorted, ?_⟩\n    intro c hc\n    have := PV_Op134_CellOrder{i:02}.bounds c hc\n    omega\n'
for i in range(58,-1,-1):
 rhs=f'b{i+1}' if i==58 else f'h{i+1}'
 s+=f'  have h{i} := append_bounds b{i} (by decide) (by decide) {rhs}\n'
s+='  exact h0\n\ntheorem nodup : PV_CBM_CellsSpec.literals.Nodup := PV_Op134_Order.nodup ordered_bounds.1\n'
s+='''theorem complete (row column : Nat) (hr : row < 1024) (hc : column < 16)
    (hf : PV_CBM_InventoryShape.free row column) :
    ∃ c ∈ PV_CBM_CellsSpec.literals, c.row.val = row ∧ c.column.val = column := by
  exact PV_Op134_Coverage.complete _ nodup
    (by intro c hc; have h := ordered_bounds.2 c hc; exact ⟨h.2.2.1,h.2.2.2⟩)
    PV_CBM_CellsSpec.all_free PV_CBM_CellsSpec.length row column hr hc hf
#print axioms ordered_bounds
#print axioms nodup
#print axioms complete
end R1Z.PV_Op134_Inventory
'''
p=lean/'PV_Op134_Inventory.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('CHECK' if '--check' in sys.argv else 'GENERATED','inventory composition')
