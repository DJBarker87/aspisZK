"""Emit bounded native arithmetic cuts for the retained final dot table.
No successful parent or flush equality is hypothesized by these leaves.
"""
from pathlib import Path
import json,sys
P=Path(__file__).parent;R=P.parents[1]
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')}
exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
d=json.loads((R/'evidence/fixture-tx2q-20261027/JGt_DOT_PREFLIGHT.json').read_text())
w=x['wide'];sums=[[0]*8];products=[]
for field,weight in zip(d['fields'],d['weights']):
 prod=x['mul'](field,weight+[0]*4);products.append(prod);sums.append(x['add'](sums[-1],prod))
assert sums[-1]==d['rhs']
def write(name,s):
 p=R/'lean'/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,name
 else:p.write_text(s)
s='import JGv_WeightsData\n'+''.join(f'import JGo_TX2_Message{i:02}\n' for i in range(0,64,8))
s+='set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JGv_DotData\nopen Aeneas Aeneas.Std\nabbrev E := SAQ_WideABI.E\n'
for i,v in enumerate(sums):s+=f'def v{i:02} : E := {w(v)}\n'
s+='def state : Nat → E\n'+''.join(f'  | {i} => v{i:02}\n' for i in range(64))+'  | _ => v64\n'
s+='def fields : List E := ['+','.join(f'JGo_TX2_Message{j//8*8:02}.value{j:02}' for j in range(64))+']\n'
s+='theorem length : fields.length=64 := by rfl\n#print axioms length\n'
s+="def field (i : Fin 64) : E := fields[i.val]'(by rw [length];exact i.isLt)\n"
s+='def term (i : Fin 64) : OraclePortCheckpointAbiC5.E :=\n  CheckpointBytes5Output.ofE (field i)*LiteralOpeningView.eK (CheckpointBytes5Output.ofK (JGv_WeightsData.cell i))\n'
s+='end AspisR1.JGv_DotData\nend\n';write('JGv_DotData',s)
for block in range(4):
 name=f'JGv_DotProducts{block}'
 s='import JGv_DotData\nimport SAQ_MixedSource\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+name+'\nopen Aeneas Aeneas.Std Result\nopen JGv_DotData\n'
 for j in range(16*block,16*block+16):
  s+=f'def product{j:02} : E := {w(products[j])}\n'
  s+=f'theorem mul{j:02} : SAQ_MixedSource.mulE (field ⟨{j},by decide⟩) (JGv_WeightsData.cell ⟨{j},by decide⟩)=ok product{j:02} := by with_unfolding_all rfl\n#print axioms mul{j:02}\n'
  s+=f'theorem add{j:02} : FIn_Primitives.add v{j:02} product{j:02}=ok v{j+1:02} := by with_unfolding_all rfl\n#print axioms add{j:02}\n'
  s+=f'''theorem step{j:02} : CheckpointBytes5Output.ofE (state {j+1})=
    CheckpointBytes5Output.ofE (state {j})+term ⟨{j},by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message{j//8*8:02}.canonical{j:02}
    (JGv_WeightsData.canonical ⟨{j},by decide⟩) mul{j:02}
  exact (FIn_Primitives.add_value _ _ _ add{j:02}).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v{j:02}+t) product.1)
#print axioms step{j:02}
'''
 s+=f'end AspisR1.{name}\nend\n';write(name,s)
print('DotData and4 native arithmetic chunks,16 independent leaf terms each')
