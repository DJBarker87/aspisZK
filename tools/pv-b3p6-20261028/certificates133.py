"""Generate small membership and interval facts; compose by symbolic theorems."""
import runpy,sys
from pathlib import Path
v=runpy.run_path('tools/pv-b3p6-20261028/specialize133.py');eps=v['eps'];exp=v['expected']
D=Path('evidence/pv-b3p6-20261028/lean')
ins=[eps[i:i+16] for i in range(0,len(eps),16)];outs=[exp[i:i+16] for i in range(0,len(exp),16)]
def choose(n,i,inner):
 for k in range(n-1,-1,-1):
  if k==i:
   if k<n-1:inner=f'Or.inl ({inner})'
  elif k<i:inner=f'Or.inr ({inner})'
 return inner
for direction,blocks,target in [('Input',ins,outs),('Output',outs,ins)]:
 source='input' if direction=='Input' else 'expected';dest='expected' if direction=='Input' else 'input'
 ns=f'PV_B3P_{direction}Members133'
 s=f'import PV_B3P_Sorted133\nnamespace {ns}\nopen PV_B3P_Sorted133\nset_option autoImplicit false\n'
 for i,chunk in enumerate(blocks):
  s+=f'theorem block{i} : ({chunk} : List Nat) ⊆ {dest} := by\n  intro x hx\n  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx\n  rcases hx with '+ ' | '.join('rfl' for _ in chunk)+'\n'
  for x in chunk:
   j=next(j for j,c in enumerate(target) if x in c)
   s+=f'  · simp only [PV_B3P_Sorted133.{dest},List.mem_append]\n    exact {choose(len(target),j,"by decide")}\n'
  s+=f'#print axioms block{i}\n'
 s+=f'theorem subset : {source} ⊆ {dest} := by\n  intro x hx\n  simp only [PV_B3P_Sorted133.{source},List.mem_append] at hx\n  rcases hx with '+ ' | '.join('h' for _ in blocks)+'\n'
 for i in range(len(blocks)):s+=f'  · exact block{i} h\n'
 s+=f'#print axioms subset\nend {ns}\n'
 p=D/f'{ns}.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
ns='PV_B3P_Ordered133'
s=f'import PV_B3P_Canonical133\nimport PV_B3P_Sorted133\nnamespace {ns}\nopen PV_B3P_Canonical133\nset_option autoImplicit false\n'
los=[0]+[c[0] for c in outs[1:]]
for i,chunk in enumerate(outs):
 hi=outs[i+1][0] if i+1<len(outs) else 1024
 s+=f'theorem block{i} : Block {chunk} {los[i]} {hi} := by unfold Block; decide\n#print axioms block{i}\n'
for i in range(len(outs)-1,-1,-1):
 suffix=v['rightappend']([str(c) for c in outs[i:]])
 s+=f'theorem tail{i} : Block ({suffix}) {los[i]} 1024 := '
 if i==len(outs)-1:s+=f'block{i}\n'
 else:s+=f'join _ _ _ _ _ block{i} tail{i+1} (by decide) (by decide)\n'
 s+=f'#print axioms tail{i}\n'
s+='theorem expected_ordered : PV_B3P_Sorted133.expected.Pairwise (· < ·) := tail0.1\n#print axioms expected_ordered\nend '+ns+'\n'
p=D/f'{ns}.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
