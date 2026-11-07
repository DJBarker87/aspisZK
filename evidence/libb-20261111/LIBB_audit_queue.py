"""Serial required own-root ax2 audits; never rerun an existing attempt."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
start,first,last=map(int,sys.argv[1:])
roots=json.loads((E/'LIBB_AUDIT_ROOTS.json').read_text())['groups']
for k,g in enumerate(range(first,last),start):
 assert g<len(roots) and k<=300
 a=f'LIBB_L{k:03d}'
 r=subprocess.run([sys.executable,str(E/'LIBB_run.py'),a,'audit','proof'+str(g)])
 if r.returncode:sys.exit(r.returncode)
 raw=json.loads((E/'LIBB_audit'/('proof'+str(g))/('proof'+str(g)+'.json')).read_text())
 assert len(raw['results'])==1
 result=raw['results'][0]
 assert result['root']==roots[g][0]
 assert set(result['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'},result
 print('audited '+result['root'],flush=True)
 if (g-first+1)%10==0 or g+1==last:
  assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file()),'Oversize receipt'
  subprocess.run(['git','add','evidence/libb-20261111'],check=True)
  subprocess.run(['git','commit','-m','Audit TX2 library roots '+str(g-first+1)+' of '+str(last-first)],check=True,stdout=subprocess.DEVNULL)
