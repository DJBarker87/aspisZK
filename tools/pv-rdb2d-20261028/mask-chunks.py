from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];P=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdb2d-20261028'
s=(R/'tools/pv-b3p6-20261028/reference133.rs').read_text().split('    [',1)[1].split(']',1)[0];rows=list(map(int,s.split(', ')));assert len(rows)==214
state=[0]*64;manifest=[]
for i,start in enumerate(range(0,len(rows),16)):
 chunk=rows[start:start+16];before=state[:]
 for row in chunk:state[row//16]|=1<<(row%16)
 name=f'PV_RDB2D_MaskChunk{i:02}'
 imp='PV_RDB2D_MasksLoop' if i==0 else f'PV_RDB2D_MaskChunk{i-1:02}'
 def masks(xs):return '['+', '.join(f'{x}#16'for x in xs)+']'
 text=f'''import R1Z.{imp}
namespace R1Z.{name}
open PV_RDB2D_MasksLoop
set_option autoImplicit false
def rows : List Nat := {chunk}
def before : Masks := {masks(before)}
def after : Masks := {masks(state)}
theorem value : run rows before=after := by decide
theorem bounds : ∀ x ∈ rows, x<1024 := by decide
#print axioms value
#print axioms bounds
end R1Z.{name}
'''
 (P/(name+'.lean')).write_text(text);manifest.append(dict(module='R1Z/'+name,rows=chunk,before=before,after=state[:]))
(E/'mask-chunks.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('chunks',len(manifest),'final',state)
