"""Named per-height source-count recurrence cells, never full recurrence reduction."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
data=json.loads((P/'JGf_MERKLE_PREFLIGHT.json').read_text())
files={}
for t in [0,2]:
 tree=data['trees'][t];front=sorted(r['index'] for r in tree['hashes'][:12]);steps=[]
 for h in range(18):
  parents=sorted(set(i//2 for i in front));missing=2*len(parents)-len(front)
  steps.append((front,parents,missing));front=parents
 assert sum(r[2] for r in steps)==tree['consumed']
 ns=f'JGf_TX2_Count{t}';s='import JFo_Prepared\nimport Port4B_Install\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+ns+'\nopen Aeneas Aeneas.Std Result OraclePortFrozenOrder MultiproofConeCountGroups MultiproofConeCountLevels\n'
 ls=lambda xs:'['+','.join(map(str,xs))+']'
 for h,(before,after,n) in enumerate(steps):
  s+=f'def indices{h:02} : List Nat := {ls(before)}\n'
 s+=f'def indices18 : List Nat := {ls(front)}\n'
 for h,(before,after,n) in enumerate(steps):
  s+=f'theorem level{h:02} : sourceLevel indices{h:02}.length indices{h:02}=(indices{h+1:02},{n}) := by rfl\n#print axioms level{h:02}\n'
 for h in reversed(range(18)):
  n=sum(row[2] for row in steps[h:]);c=steps[h][2]
  s+=f'theorem total{h:02} : sourceCount {18-h} indices{h:02}={n} := by\n  rw [sourceCount,level{h:02}]\n'
  if h==17:s+='  rfl\n'
  else:s+=f'  change {c}+sourceCount {17-h} indices{h+1:02}={n}\n  rw [total{h+1:02}]\n'
  s+=f'#print axioms total{h:02}\n'
 s+='def frontier : Slice U32 := ⟨'+ls([str(i)+'#u32' for i in steps[0][0]])+',by decide⟩\n'
 s+='theorem values : frontier.val.map UScalar.val=indices00 := by rfl\n#print axioms values\n'
 s+='theorem well : wellFormed indices00 := by decide\n#print axioms well\n'
 s+=f'''theorem source : Port4B_Install.leaves.op11 .Two frontier=ok (some {tree['consumed']}#usize) := by
  change Port4B_CountInstall.nodeCount .Two frontier=_
  rw [Port4B_CountInstall.nodeCount,values,dif_pos well]
  congr 2
  apply UScalar.eq_of_val_eq
  change sourceCount 18 indices00={tree['consumed']}
  exact total00
#print axioms source
end AspisR1.{ns}
end
'''
 files[R/'lean'/(ns+'.lean')]=s
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('two count modules; eighteen individually named steps each; no full recurrence reduction')
