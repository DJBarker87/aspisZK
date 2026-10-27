"""Generate cell-sized reductions of the actual query/flush field recurrence.
Factors are named symbolic cuts; no parent execution or whole buffer is reduced.
"""
from pathlib import Path
import json,re,sys
P=Path(__file__).parent;R=P.parents[1]
d=json.loads((R/'evidence/fixture-tx2q-20261027/JGt_DOT_PREFLIGHT.json').read_text())
initial=[]
for j in range(64):
 text=(R/'lean'/f'JFq_Weights{j//4:02}.lean').read_text().split(f'namespace AspisR1.JFq_Weight{j:02}\n')[1].split('end AspisR1.')[0]
 match=re.search(r'def decoded[^\n]*:= (.*)',text)
 initial.append(list(map(int,re.findall(r'(\d+)#u32',match.group(1)))))
s='import JGv_QueryScalars\nimport JGv_QueryRows\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JGv_PowerLimbs\nopen Aeneas Aeneas.Std\n'
for i in range(12):
 for k in range(4):
  value=d['states'][i]['power'][k]
  s+=f'theorem p{i}_{k} : (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK (JGv_QueryScalars.power {i})) ⟨{k},by decide⟩).val={value} := by rfl\n#print axioms p{i}_{k}\n'
s+='end AspisR1.JGv_PowerLimbs\nend\n'
def write(name,s):
 p=R/'lean'/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,name
 else:p.write_text(s)
write('JGv_PowerLimbs',s)
for block in range(16):
 name=f'JGv_WeightCells{block:02}'
 s='import JGv_PowerLimbs\n'+''.join(f'import JGv_BasisFactors{i}\n' for i in range(12))
 s+=f'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen Aeneas Aeneas.Std\nabbrev F := JGv_QueryRows.F\n'
 for j in range(4*block,4*block+4):
  bits=[b for b in range(6) if j>>b&1]
  for i in range(12):
   node=f'(S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query {i})))'
   setstr='({'+','.join(map(str,bits))+'} : Finset Nat)' if bits else '(∅ : Finset Nat)'
   s+=f'theorem basis{i}_{j} : AspisCircleTensorBinding.naturalLineValue {node} {j}=({d["bases"][i][j]} : F) := by\n'
   s+=f'  change (∏ bit ∈ {setstr},AspisCircleTensorBinding.doubledFactor {node} bit)=_\n'
   s+='  norm_num ['+','.join(f'JGv_BasisFactors{i}.factor{b}' for b in bits)+(',' if bits else '')+','.join(f'JGv_BasisFactors{i}.x{b}' for b in bits)+']\n  all_goals apply (ZMod.natCast_eq_natCast_iff\' _ _ _).mpr\n  all_goals norm_num\n'
   s+=f'#print axioms basis{i}_{j}\n'
  for k in range(4):
   s+=f'theorem initial{j}_{k} : JFn_PendingHistory.sum {j} ⟨{k},by decide⟩={initial[j][k]} := by rfl\n#print axioms initial{j}_{k}\n'
   s+=f'theorem cell{j}_{k} : JGv_QueryRows.weights 12 {j} ⟨{k},by decide⟩=({d["weights"][j][k]} : F) := by\n'
   s+='  simp only [JGv_QueryRows.weights,'+f'initial{j}_{k},'+','.join(f'basis{i}_{j}' for i in range(12))+','+','.join(f'JGv_PowerLimbs.p{i}_{k}' for i in range(12))+']\n  norm_num\n  all_goals apply (ZMod.natCast_eq_natCast_iff\' _ _ _).mpr\n  all_goals norm_num\n'
   s+=f'#print axioms cell{j}_{k}\n'
 s+=f'end AspisR1.{name}\nend\n'
 write(name,s)
print('Power limbs and16 four-cell field recurrence chunks')
