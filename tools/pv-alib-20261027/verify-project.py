"""Verify the focused project import cone against committed source pins."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027'; L=R/'docs/research/v8-r0-zk-20261009/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
ext={x['module'].replace('/','.') for x in json.loads((E/'resume3-external-manifest.json').read_text())}
ejr=json.loads(subprocess.check_output(['git','show','research:evidence/envj-rebuild-20261026/EJR_final-inventory.json']))
pins={x['module'].replace('/','.'):dict(path=x['resolution']['path'],sha256=x['sha256'],record='research:evidence/envj-rebuild-20261026/EJR_final-inventory.json') for x in ejr['selected'] if x.get('resolution')}
# Existing committed candidate source freezes; no name search chooses a source.
cp='evidence/pv-cblib-20261027/manifest9-source-pins.json';cj=json.loads((R/cp).read_text())
for x in cj['modules']:
 m=x['module'].replace('/','.');p='docs/research/v8-r0-zk-20261009/lean/'+x['module']+'.lean'
 pins.setdefault(m,dict(path=p,sha256=x['sha256'],record=cp,revision=cj['freeze_revision']))
p='evidence/pv-cbmid-20261027/LEAN-IMPORT-PROVENANCE.json'
for m,x in json.loads((R/p).read_text()).items():
 if m.startswith('ProverRwFull'):
  pins.setdefault('R1Z.'+m,dict(path=x['local_source'],sha256=x['local_sha256'],record=p))
p='evidence/privacy-recount-20261026/source-manifest.json'
for x in json.loads((R/p).read_text()):
 if x.get('exit')==0 and x['path'].endswith('/ProverRwFullFuns.lean'):
  pins.setdefault('R1Z.ProverRwFullFuns',dict(path=x['path'],sha256=x['sha256'],record=p,revision=x['revision']))
rows={};missing=[]
def visit(m):
 if m in ext or m in rows:return
 if m.startswith('R1Z.PV_AL_'):
  p=L/(m.replace('.','/')+'.lean');s=p.read_bytes();x=dict(path=str(p.relative_to(R)),sha256=sha(s),record='assigned own PV_AL source at current revision')
 elif m in pins:
  x=pins[m].copy();p=R/x['path'];s=p.read_bytes()
  if sha(s)!=x['sha256']:raise RuntimeError(('source mismatch',m,sha(s),x))
 else:missing.append(m);rows[m]={'missing':True};return
 rows[m]=x
 imports=re.findall(r'^import\s+(\S+)',s.decode(),re.M);rows[m]['imports']=imports
 for dep in imports:visit(dep)
for m in ['R1Z.PV_AL_SplitBridge','R1Z.PV_AL_CircleSelected','R1Z.PV_AL_MoveClosure']:visit(m)
# Read-only verification of the actual cached-source cohort, without copying sources.
req={m:x for m,x in rows.items() if 'sha256' in x}
code='''from pathlib import Path
import json,hashlib
req=json.loads(REQ);base=Path('/home/dombarker/project-offloads');d=base/'codex-pv-alib-20261027'
roots=[d/'lean-sources',base/'aspis-joint-20261019/sources',base/'codex-pv-cblib-20261027/lean-sources']
rows={}
for m,x in req.items():
 p=next((r/(m.replace('.','/')+'.lean') for r in roots if (r/(m.replace('.','/')+'.lean')).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 rows[m]=dict(path=str(p),sha256=h,expected=x['sha256'],ok=h==x['sha256'])
print(json.dumps(rows))
'''.replace('REQ',repr(json.dumps(req)))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
remote=json.loads(r.stdout);bad={m:x for m,x in remote.items() if not x['ok'] and not (m.startswith('R1Z.PV_AL_') and x['path']=='None')}
j=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scope='all three focused candidate cones; cached sources only',sources=rows,host_source_check=remote,missing=missing,mismatches=bad,ok=not missing and not bad)
(E/'resume3-project-preflight.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(dict(count=len(rows),missing=missing,mismatches=bad,ok=j['ok'])))
