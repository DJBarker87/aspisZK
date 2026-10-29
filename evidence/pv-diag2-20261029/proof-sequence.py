"""Add and check one named source-control lemma at a time; never retry unchanged.
--check validates the final source against the committed proof plan.
"""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;plan=json.loads((E/sys.argv[1]).read_text());out=E/(plan['module']+'.lean')
def source(n):return plan['base']+'\n\n'+'\n\n'.join(plan['steps'][:n])+'\nend PV_DIAG2\n'
if '--check' in sys.argv:
 assert out.read_text()==source(len(plan['steps']));print('checked',plan['module'],len(plan['steps']),'lemmas');raise SystemExit(0)
start=int(sys.argv[2]);offset=int(sys.argv[3]) if len(sys.argv)>3 else 0
for i in range(offset,len(plan['steps'])):
 out.write_text(source(i+1));n=start+i-offset
 r=subprocess.run([sys.executable,str(E/'focus.py'),str(n),plan['module']])
 if r.returncode:print('STOP changed lemma',i,'attempt',n,flush=True);raise SystemExit(r.returncode)
 print('CHECKED',n,plan['module'],'new lemma',i+1,flush=True)
