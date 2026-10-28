from pathlib import Path
import json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
D=json.loads((P/'JHl_WEIGHT_PREFLIGHT.json').read_text());assert all(r['match'] for r in D['rows'])
def lit(a):return '⟨⟨'+','.join(map(str,a[:2]))+'⟩,⟨'+','.join(map(str,a[2:]))+'⟩⟩'
files={}
for start in [1]+list(range(3,64,4)):
 end=2 if start==1 else min(start+3,63);name=f'JHl_Weight{start:02}_{end:02}'
 s='import JHl_WeightFormula\n'+''.join(f'import JFq_Weights{b:02}\n' for b in sorted(set(j//4 for j in range(start,end+1))))+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField
'''
 for j in range(start,end+1):
  row=D['rows'][j]
  for i in range(10):
   s+=f'''\ntheorem basis{j:02}_{i:02} : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis{i:02}.node) {j}=({row['basis'][i]} : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,'''+','.join(f'JHl_Basis{i:02}.factor{k}' for k in range(6))+'''] <;> decide
'''+f'#print axioms basis{j:02}_{i:02}\n'
  s+=f'''\ntheorem source{j:02} : totalAt 10 {j}=CheckpointBytes5Output.ofK JFq_Weight{j:02}.scalar := by
  simp only [totalAt,contribution,node,'''+','.join(f'show ({i} : Nat)<10 from by decide' for i in range(10))+''',dif_pos]
  rw ['''+','.join(f'basis{j:02}_{i:02}' for i in range(10))+''']
  change (0 : K)'''+''.join(f'+ '+('(1 : K)' if i==0 else f'JHk_Rhs{i-1:02}.power')+f'*scalar {row["basis"][i]}' for i in range(10))+'='+lit(row['target'])+'''
  unfold scalar '''+' '.join(f'JHk_Rhs{i:02}.power' for i in range(9))+'''
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
'''+f'#print axioms source{j:02}\n'
 s+=f'end AspisR1.{name}\nend\n';files[name]=s
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('17 small-group weight modules validated; all numeric preflight weights match')
