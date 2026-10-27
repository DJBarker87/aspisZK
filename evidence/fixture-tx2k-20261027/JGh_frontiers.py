"""Sparse named frontier certificates; no 2^18 occupancy traversal by reduction."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
data=json.loads((R/'evidence/fixture-tx2j-20261027/JGf_MERKLE_PREFLIGHT.json').read_text())
head='set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JGh_TX2_Frontiers\nopen OraclePortSelectedDraft OracleDecisionMultiBuild\n'
end='end AspisR1.JGh_TX2_Frontiers\nend\n'
base='import JGh_TX2_NodeViews\nimport JGc_TX2_M2Layout\n'+head
base+='theorem unoccupied (is : List Nat) (h b : Nat) (no : ¬Occupied is h b) : frontier is h b=[(h,b)] := by\n  cases h <;> simp only [frontier,if_neg no]\n#print axioms unoccupied\n'
prev={};streams={}
for k in [0,2]:
 ro='JGf_TX2_M0Roots' if k==0 else 'JGc_TX2_M2Roots';prev[k]={row['index']:i for i,row in enumerate(data['trees'][k]['hashes'][:12])};streams[k]=[]
 for b,i in prev[k].items():
  base+=f'def coords{k}_{i:03} : List (Nat×Nat) := []\ntheorem front{k}_{i:03} : frontier {ro}.indices 0 {b}=coords{k}_{i:03} := by\n  rw [frontier,if_pos (by decide : Occupied {ro}.indices 0 {b})]\n#print axioms front{k}_{i:03}\n'
files={R/'lean/JGh_TX2_FrontierBase.lean':base+end}
for h in range(18):
 name=f'JGh_TX2_FrontierHeight{h:02}';last='JGh_TX2_FrontierBase' if h==0 else f'JGh_TX2_FrontierHeight{h-1:02}'
 s=f'import {last}\n'+head
 for k in [0,2]:
  ro='JGf_TX2_M0Roots' if k==0 else 'JGc_TX2_M2Roots';after={}
  for i,row in enumerate(data['trees'][k]['hashes']):
   if row['kind']!='parent' or row['level']!=h:continue
   b=row['index']*2**(h+1);parts=[];rewrites=[]
   for side in range(2):
    cb=(2*row['index']+side)*2**h;j=prev[k].get(2*row['index']+side)
    if j is not None:parts.append(f'coords{k}_{j:03}');rewrites.append(f'front{k}_{j:03}')
    else:
     parts.append(f'[(\u0020{h},{cb})]');rewrites.append(f'unoccupied {ro}.indices {h} {cb} (by decide)');streams[k].append((h,cb))
   s+=f'def coords{k}_{i:03} : List (Nat×Nat) := '+ '++'.join(parts)+'\n'
   s+=f'theorem front{k}_{i:03} : frontier {ro}.indices {h+1} {b}=coords{k}_{i:03} := by\n  rw [frontier,if_pos (by decide : Occupied {ro}.indices {h+1} {b})]\n  simp only [Nat.reducePow,Nat.reduceAdd]\n  rw ['+','.join(rewrites)+f']\n  rfl\n#print axioms front{k}_{i:03}\n'
   after[row['index']]=i
  prev[k]=after
 sib=(P/'JGh_UNCHECKED'/f'JGh_TX2_Siblings{h:02}.lean.txt').read_text()
 files[R/'lean'/(name+'.lean')]=f'import {last}\n'+sib[sib.index('set_option'):]+s[len(f'import {last}\n'):]+end
s='import JGh_TX2_FrontierHeight17\nimport JGh_TX2_FrontierOrder\n'+head
for k in [0,2]:
 ro='JGf_TX2_M0Roots' if k==0 else 'JGc_TX2_M2Roots';last=prev[k][0]
 stream=sorted(streams[k]);literal='['+','.join(f'({h},{b})' for h,b in stream)+']'
 s+=f'def stream{k} : List (Nat×Nat) := {literal}\n'
 s+=f'theorem ordered{k} : orderedFrontier {ro}.indices=stream{k} := by\n  rw [orderedFrontier,front{k}_{last:03}]\n  rfl\n#print axioms ordered{k}\n'
 s+=f'theorem count{k} : MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count{k}.indices00=(orderedFrontier {ro}.indices).length := by\n  rw [JGf_TX2_Count{k}.total00,ordered{k}]\n  rfl\n#print axioms count{k}\n'
 s+=f'theorem length{k} : stream{k}.length={len(stream)} := rfl\n#print axioms length{k}\n'
files[R/'lean/JGh_TX2_FrontierStream.lean']=s+end
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('frontier generator:',len(files),'modules; named sparse nodes then sorted163/141 sibling streams')
