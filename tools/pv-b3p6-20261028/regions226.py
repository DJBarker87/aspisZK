"""Emit named symbolic laws for each serializer byte region, without unfolding
field arithmetic or enumerating the concrete 1472-byte buffer."""
from pathlib import Path
D=Path(__file__).resolve().parents[2]/'evidence/pv-b3p6-20261028/lean'
for name in ['ByteTotal','ByteOutcome']:
 p=D/f'PV_B3P_{name}226V3.lean';s=p.read_text()
 a=s.index('  unfold reference226.byte_at');tail=s.index('\n#print axioms',a)
 proof='  unfold reference226.byte_at\n  cases hp : p.withdrawal with\n'
 def solve(ind,j,b):
  if j in [0,1,5,8,10]:return ind+'exact ⟨_,rfl⟩\n'
  if (j==6 and b=='true') or (j==9 and b=='false'):
   return ind+'exfalso; scalar_tac\n'
  if j in [4,9]:
   if name=='ByteOutcome':return ind+'exact PV_B3P_FieldResult226V3.no_outer_failure _ _\n'
   return ind+'apply field_total\n'+ind+f'exact {"hs" if j==4 else "hm"}\n'
  helper='Frontier' if j in [11,13] else 'Digest'
  nm=f'PV_B3P_{helper}{"Total" if name=="ByteTotal" else "Outcome"}226V3.{"success" if name=="ByteTotal" else "no_outer_failure"}'
  q=ind+f'apply {nm}\n'+ind+'· repeat first\n'+ind+'    | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]\n'+ind+'    | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]\n'+ind+'  scalar_tac\n'
  if name=='ByteTotal':q+=ind+'· exact '+{2:'ha',3:'hn',6:'hr',7:'hc',11:'hf',12:'hroot',13:'hnf'}[j]+'\n'
  return q
 for b,n,change,index,front in [('false',1455,102,135,143),('true',1427,70,107,115)]:
  proof+=f'''  | {b} =>
    simp only [hp,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
      c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
'''
  conditions=[f'i ≥ {n}#usize','i = 0#usize','i < 33#usize','i < 65#usize','i < 69#usize','i = 69#usize',f'i < {change}#usize',f'i < {change+32}#usize',f'i = {change+32}#usize',f'i < {index}#usize',f'i < {front}#usize',f'i < {front+640}#usize',f'i < {front+672}#usize']
  ind='    '
  for j,c in enumerate(conditions):
   proof+=ind+f'by_cases h{j} : {c}\n'+ind+f'· simp only [h{j},↓reduceIte]\n'+solve(ind+'  ',j,b)+ind+f'· simp only [h{j},↓reduceIte]\n';ind+='  '
  proof+=solve(ind,13,b)
 p.write_text(s[:a]+proof+s[tail:])
