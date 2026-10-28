"""Named scalar projections for the sparse final state; no array/run reduction."""
from pathlib import Path
import re,sys,json,hashlib
D=Path(__file__).resolve().parent;L=D/'lean'
def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
raw=(L/'PV_B3_Forest_134_Funs.lean').read_text();table=raw.split('Array.make 136#usize [',1)[1].split(']',1)[0]
links=[tuple(map(int,m)) for m in re.findall(r'\((\d+)#u16,\s*(\d+)#u16\)',table)]
points=sorted({v for pair in links for v in pair})
ref=D.parents[1]/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Op134_Masks.lean'
reftext=ref.read_text();values=list(map(int,re.findall(r'(\d+)#u16',reftext.split('Array.make 64#usize [',1)[1].split(']',1)[0])))
assert len(values)==64
calc=[0]*64
for a,b in links:
 for x in [a,b]:calc[x//16]|=1<<(x%16)
assert calc==values
s='''import PV_B3_MaskSparseBit
namespace PV_B3_MaskSparseMarks
open Aeneas Aeneas.Std PV_B3_MaskSparseStep
set_option autoImplicit false
'''
for p in points:
 s+=f'''theorem mark{p:04} (m : Nat → U16) (k : Nat) :
    (mark m {p}#usize k).val = if k = {p//16} then (m k).val ||| {1<<(p%16)} else (m k).val := by
  simpa only [show ({p}#usize).val = {p} from rfl,
    show {p} / 16 = {p//16} from by decide,
    show 2^({p}%16) = {1<<(p%16)} from by decide] using
    PV_B3_MaskSparseBit.mark_value m {p}#usize k
#print axioms mark{p:04}
'''
s+='end PV_B3_MaskSparseMarks\n';emit(L/'PV_B3_MaskSparseMarks.lean',s)
for group in range(8):
 mod=f'PV_B3_MaskSparseValues{group}'
 s=f'''import PV_B3_MaskSparseMarks
import PV_B3_MaskSparseStates
namespace {mod}
open Aeneas Aeneas.Std PV_B3_MaskSparseStates PV_B3_MaskSparseMarks
set_option autoImplicit false
'''
 for k in range(group*8,group*8+8):
  s+=f'theorem cell{k:02} : (M136 {k}).val = {values[k]} := by\n'
  for top in range(136,0,-8):
   indices=list(range(top,max(0,top-8),-1));ps=sorted({v for i in indices for v in links[i-1]})
   args=[f'M{i:03}' for i in indices]+[f'mark{p:04}' for p in ps]
   for b in sorted({p//16 for p in ps}):
    args.append(f'if_pos (by decide : ({k} : Nat) = {b})' if k==b else f'if_neg (by decide : ¬(({k} : Nat) = {b}))')
   s+='  simp only ['+', '.join(args)+']\n'
  s+='  simp only [M000]\n  all_goals decide\n'+f'#print axioms cell{k:02}\n'
 s+=f'end {mod}\n';emit(L/(mod+'.lean'),s)
meta={'reference_source_sha256':hashlib.sha256(ref.read_bytes()).hexdigest(),'reference_matches_accepted_source':'evidence/pv-op134-20261027/50108-source.lean.txt','literal_preflight_equal':True,'blocks':64,'distinct_endpoints':len(points),'method':'named mark-value transports; 8 links (16 mask updates) per symbolic batch; explicit tiny block comparisons; no array or whole-run kernel reduction'}
emit(D/'sparse134-values-preflight.json',json.dumps(meta,indent=2)+'\n')
print(meta)
