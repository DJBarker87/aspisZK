"""Generate deterministic CPS proofs for fixed circle rows; no broad search/reduction."""
from pathlib import Path
import re
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for i in [3,4]:
 p=L/f'PV_B2_C_ConstructorRow{i}.lean';s=p.read_text();a=s.index(' := by\n',s.index(f'theorem row{i}_total'))+len(' := by\n');b=s.index(f'#print axioms row{i}_total',a)
 body=s.split(' : Result Factors := do\n',1)[1].split(f'\ntheorem row{i}_total',1)[0]
 steps=[f'  unfold row{i}']
 for m in re.finditer(r'^  let (.*?) ←\s*\n?\s*(.*)',body,re.M):
  name,term=m.groups()
  if term.startswith('Array.index_usize'):leaf='read _ _ (by decide)'
  elif term.startswith('Array.index_mut_usize'):leaf='borrow _ _ (by decide)'
  elif term.startswith('Array.update'):leaf='write _ _ _ (by decide)'
  elif term.startswith('host_weights.double'):leaf='PV_B2_C_WeightsTotal.double _'
  elif term.startswith('aspis_core.field.QM31.mul'):leaf='⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩'
  else:raise Exception(term)
  steps.append('  apply PV_B2_C_ArrayTotal.bind _ _ ('+leaf+')')
  steps.append(('  rintro ⟨'+name[1:-1]+'⟩') if name.startswith('(') else '  intro '+('unused' if name=='_' else name))
 steps.append('  exact ⟨_,rfl⟩')
 p.write_text(s[:a]+'\n'.join(steps)+'\n'+s[b:])
