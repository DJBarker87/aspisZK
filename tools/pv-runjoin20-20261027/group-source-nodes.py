from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';steps=list(range(5,25))+[54,55,56,33]+list(range(34,54));groups=[steps[i:i+4] for i in range(0,len(steps),4)]
owner={h:group[0] for group in groups for h in group}
for group in groups:
 imports=[];bodies=[]
 for h in group:
  p=R/'evidence/pv-runjoin20-20261027/node-drafts'/f'PV_RunJoin_SourceNode{h:02}20.lean.txt';s=p.read_text()
  for l in s.splitlines():
   if not l.startswith('import '):continue
   m=re.fullmatch(r'import R1Z.PV_RunJoin_SourceNode(\d+)20',l)
   if m and int(m[1]) in group:continue
   if m and int(m[1]) in owner:l=f'import R1Z.PV_RunJoin_SourceNodes{owner[int(m[1])]:02}20'
   imports.append(l)
  bodies.append(s[s.index('set_option'):])
 out='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies)
 p=L/f'PV_RunJoin_SourceNodes{group[0]:02}20.lean'
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
print(json.dumps(groups))
