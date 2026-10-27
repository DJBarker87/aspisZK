"""Constructor source association via deterministic congruence at each fixed cut.
All intermediate monadic values remain symbolic. No whole-constructor reduction.
"""
from pathlib import Path
import re,sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');p=L/'PV_B2_C_ConstructorSuccess.lean';s=p.read_text()
env=(L/'PV_B2_C_ConstructorEnvironment.lean').read_text();raw=env.split('def host_weights.Weights.new',1)[1].split('  := do\n',1)[1].split('\n\n\n#print axioms host_weights.Weights.new',1)[0]
commands=list(re.finditer(r'^  let (.*?) (←|:=)',raw,re.M));boundaries={'a2':0,'a18':1,'a34':2,'scp':3,'scp1':4};stages={}
for i in range(5):
 b=(L/f'PV_B2_C_ConstructorStage{i}.lean').read_text().split(' := do\n',1)[1].split(f'\ntheorem stage{i}_eq',1)[0]
 stages[i]=b
steps=['  unfold host_weights.Weights.new staged'];active=None;unused=0;needs_change=False
for j,m in enumerate(commands):
 name=m[1];op=m[2]
 if op==':=':
  end=commands[j+1].start() if j+1<len(commands) else len(raw)
  pure=raw[m.start():end].strip().splitlines()[0]
  steps.append('  '+pure);needs_change=True;continue
 if name in boundaries:
  active=boundaries[name];steps.append(f'  unfold stage{active}');needs_change=True
 if active is not None and needs_change:
  b=stages[active];pos=re.search(r'^  let '+re.escape(name)+r' ←',b,re.M);assert pos,name
  rhs=b[pos.start():]
  steps.append('  change (do\n'+raw[m.start():]+') = (do\n'+rhs+')')
 needs_change=name.startswith('(')
 steps.append('  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr')
 if name.startswith('('):steps.append('  rintro ⟨'+name[1:-1]+'⟩ _')
 elif name=='_':steps.append('  intro unused'+str(unused)+' _');unused+=1
 else:steps.append('  intro '+name+' _')
 if name=='q1':steps.append('  let extra : Array K 2#usize := Array.make 2#usize [q,q1]')
steps.append('  rfl')
a=s.index(' := by\n',s.index('theorem new_eq_staged'))+len(' := by\n');b=s.index('\ntheorem staged_total',a);s=s[:a]+'\n'.join(steps)+'\n'+s[b:]
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
