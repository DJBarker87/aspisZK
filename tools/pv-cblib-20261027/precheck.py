"""Refresh sibling source-law ownership before an operation; never claim a sibling's law."""
from pathlib import Path
import subprocess,json,datetime,sys
root=Path(__file__).resolve().parents[2];op=int(sys.argv[1]);out=root/'evidence/pv-cblib-20261027';branches=['codex/pv-cb-20261026','codex/pv-cb3-20261026'];stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
p=subprocess.run(['git','grep','-n',f'op{op}_source',*branches,'--','*.lean'],cwd=root,text=True,capture_output=True)
r={'op':op,'branches':{b:subprocess.check_output(['git','rev-parse',b],cwd=root,text=True).strip() for b in branches},'exit':p.returncode,'matches':p.stdout,'stderr':p.stderr,'status':'SKIP(sibling)' if p.returncode==0 else 'unclaimed' if p.returncode==1 else 'error'}
(out/f'op{op}-sibling-{stamp}.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'],op);sys.exit(2 if p.returncode==0 else 0 if p.returncode==1 else p.returncode)
