"""Emit six bounded symbolic Chebyshev cuts per retained TX2 node."""
from pathlib import Path
import json,sys
P=Path(__file__).parent;R=P.parents[1]
d=json.loads((R/'evidence/fixture-tx2q-20261027/JGt_DOT_PREFLIGHT.json').read_text());p=2147483647
for i,node in enumerate(d['nodes']):
 m=f'JGv_BasisFactors{i}'
 s='import JFz_TX2_ChainStep\nimport S7JoinBasisMachine\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+m+'\nopen Aeneas Aeneas.Std\nabbrev F := ZMod 2147483647\n'
 x=node
 for j in range(6):
  if j:x=(2*x*x-1)%p
  s+=f'def x{j} : F := {x}\n'
  s+=f'theorem factor{j} : AspisCircleTensorBinding.doubledFactor\n    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query {i}))) {j}=x{j} := by\n'
  if j==0:s+='  rfl\n'
  else:s+=f'  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query {i}))) {j-1})^2-1=x{j}\n  rw [factor{j-1}]\n  norm_num [x{j-1},x{j}]\n  all_goals apply (ZMod.natCast_eq_natCast_iff\' _ _ _).mpr\n  all_goals norm_num\n'
  s+=f'#print axioms factor{j}\n'
 s+=f'end AspisR1.{m}\nend\n'
 target=R/'lean'/(m+'.lean')
 if '--check' in sys.argv:assert target.read_text()==s
 else:target.write_text(s)
print('12 modules; six symbolic factor cuts each')
