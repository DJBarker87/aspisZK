from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin63-20261029'
plan=json.loads((E/'build-plan.json').read_text())
code=r'''import pathlib,json,sys,hashlib,os
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);roots=[pathlib.Path(r) for r in json.load(open(p/'J.json'))['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();copies=[]
# h6'' requires plain copies, no links to another job's objects.
for q in (p/'objects').rglob('*'):
 if q.is_symlink():
  target=q.resolve(); b=q.read_bytes();h=hashlib.sha256(b).hexdigest();tmp=q.with_name(q.name+'.pv63-copy');tmp.write_bytes(b);assert sha(tmp)==h;os.replace(tmp,q);copies.append(dict(path=str(q),old_target=str(target),sha256=h))
mods=[(v['module'],v['expected_object_sha256']) for v in x['pre']['projects']]+[(v['module'],v['expected']) for v in x['pre']['external']];checks=[]
for m,h in mods:
 rel=m.replace('.','/'); top=rel.split('/')[0];root=next((r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file()),None);q=root/(rel+'.olean') if root else None;actual=sha(q) if q and q.is_file() else None;checks.append(dict(module=m,path=str(q),expected=h,actual=actual,match=actual==h))
print(json.dumps(dict(rule="first namespace root, no per-file fallback",copies=copies,checks=checks,all_match=all(v['match'] for v in checks))))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],pre=json.loads((E/'fresh-preflight.json').read_text()))),text=True,capture_output=True)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'namespace-resolution.json').write_text(json.dumps(out,indent=2)+'\n');print('namespace checks',len(out['checks']),'plain copies',len(out['copies']),'all match',out['all_match']);assert out['all_match']
