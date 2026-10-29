"""Stage only this job's committed new modules, preserving inherited prefixes."""
from pathlib import Path
import subprocess,hashlib,json,shlex,re,sys
E=Path('evidence/pv-rj4idb-20261029');H='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
plan=json.loads((E/'build-plan.json').read_text()) if (E/'build-plan.json').exists() else dict(source_revision=rev,modules={},chunks=[])
payload={}
for name in sys.argv[1:]:
 upstream={'PV_DIAG2_Effects':'evidence/pv-diag2-20261029/PV_DIAG2_Effects.lean','PV_DIAG3_Execution':'evidence/pv-diag3-20261029/PV_DIAG3_Execution.lean'}
 upstream.update(json.loads((Path(__file__).parent/'upstream-paths.json').read_text()))
 assert name.startswith('PV_RJ4IDB_') or name in upstream
 path=upstream.get(name,'lean/'+name+'.lean');b=subprocess.check_output(['git','show',rev+':'+path]);assert not Path(path).exists() or b==Path(path).read_bytes()
 plan['modules'][name]=dict(path=path,revision=rev,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),imports=re.findall(r'^import (\S+)',b.decode(),re.M))
 payload[name]=b.decode()
(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H'])
for m,s in x['sources'].items():
 o=p/'objects'/(m+'.olean');assert not o.exists(),('existing object',m)
 (p/'sources'/(m+'.lean')).write_text(s)
(p/'build-plan.json').write_text(json.dumps(x['plan']))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,sources=payload,plan=plan)),text=True,capture_output=True);assert r.returncode==0,r.stderr
