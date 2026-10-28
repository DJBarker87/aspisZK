"""Prepare the two SHA-frozen field modules privately; never load CX objects.
This only creates this job's pinned source/object view; it launches no compiler.
"""
from pathlib import Path
import json,subprocess,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
H='/home/dombarker/project-offloads/codex-pv-l2d-20261028';P=H+'/embedding';host='dombarker@100.108.41.90'
resolution=json.loads((E/'embedding-resolution.json').read_text());sources=json.loads((E/'embedding-project-sources.json').read_text())
assert not resolution['unpinned'] and len(sources)==2
for m,s in sources.items():assert hashlib.sha256(s.encode()).hexdigest()==resolution['resolved'][m]['sha256']
# The EJR-selected raw source and complete external authority win. The J view
# currently resolves these two project objects from CX directories; reject them.
external=json.loads((E/'external-authority.json').read_text())
q=subprocess.run(['ssh',host,f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/admission-embedding-prepare.json > {H}/admission-embedding-prepare.log 2>&1\npv_status=$?\ncat {H}/admission-embedding-prepare.log\nexit $pv_status'],text=True,capture_output=True)
(E/'admission-embedding-prepare.log').write_text(q.stdout+q.stderr);a=json.loads(q.stdout.strip().splitlines()[-1]);assert q.returncode==0 and a['allowed'],a
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);assert not p.exists(),'private view exists; inspect and reuse, do not recreate'
for name in ['objects','sources','external','evidence']:(p/name).mkdir(parents=True,exist_ok=True)
checks=[]
for v in x['external']:
 m=v['module'].replace('/','.');q=pathlib.Path(v['path']);sha=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
 row=dict(module=m,path=str(q),expected=v['object_sha256'],actual=sha,match=sha==v['object_sha256']);checks.append(row)
 if not row['match']:continue
 dest=p/'external'/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q)
 for suffix in ['.olean.private','.olean.server','.ilean','.so','.ir']:
  c=q.with_suffix(suffix)
  if c.is_file():
   dest.with_suffix(suffix).symlink_to(c)
   row.setdefault('companions',[]).append(dict(path=str(c),sha256=hashlib.sha256(c.read_bytes()).hexdigest()))
(p/'evidence/external-check.json').write_text(json.dumps(checks))
assert all(v['match'] for v in checks),'external mismatch; stop affected step'
for m,s in x['sources'].items():
 q=p/'sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==x['resolution']['resolved'][m]['sha256']
base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));base['LEAN_PATH']=str(p/'objects')+':'+str(p/'external');(p/'J.json').write_text(json.dumps(base));(p/'resolution.json').write_text(json.dumps(x['resolution']))
print(json.dumps(dict(external_count=len(checks),all_match=True,project_count=len(x['sources']),workspace=str(p),lean_path=base['LEAN_PATH'],foreign_project_objects_loaded=False)))
'''
q=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=P,external=external,sources=sources,resolution=resolution)),text=True,capture_output=True);(E/'embedding-prepare-transport.json').write_text(json.dumps(dict(exit=q.returncode,stdout=q.stdout,stderr=q.stderr),indent=2)+'\n');assert q.returncode==0,q.stderr
(E/'embedding-prepare.json').write_text(q.stdout);print(q.stdout)
q=subprocess.run(['scp','-q',host+':'+P+'/evidence/external-check.json',str(E/'embedding-external-check.json')]);assert q.returncode==0
