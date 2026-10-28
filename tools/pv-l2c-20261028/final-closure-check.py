"""Read-only closure fingerprint check; no compiles or cache mutations."""
from pathlib import Path
import json,gzip,subprocess,shlex,hashlib,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2c-20261028/resume-d355'
res=json.loads((E/'focused-resolution.json').read_text())['resolved']
cache=json.loads(gzip.decompress((E/'restored-cache.json.gz').read_bytes()))['source_and_complete_fingerprints']
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
accepted={x['module']:x for x in receipts if x['accepted'] and x['source_sha256']==res.get(x['module'],{}).get('sha256')}
roots=['PV_L2C_FocusedReplay','PV_L2C_HonestCaller','PV_L2C_HonestHelper','PV_L2C_HonestValidity','PV_L2C_HonestSumcheck','PV_L2C_ExtractedGuard','PV_L2C_ScalarBalance','PV_L2C_ComplexParser','PV_L2C_QParser','PV_L2C_ScalarCanonical']
if '--pre-audit' in sys.argv:roots=[m for m in roots if m!='PV_L2C_FocusedReplay']
seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in res[m].get('imports',[]):visit(d)
for m in roots:visit(m)
expect={}
for m in seen:
 x=res[m]
 if 'imports' not in x:expect[m]=dict(object_sha256=x['object_sha256'],authority='h4 external')
 elif m in accepted:
  a=accepted[m]
  expect[m]=dict(source_sha256=x['sha256'],authority='own accepted compile',dependencies=a['dependencies'])
 elif m in cache:
  c=cache[m];assert c['source_resolution']['sha256']==x['sha256']
  expect[m]=dict(object_sha256=c['sha256'],authority='h6 pinned reuse',dependencies={d:dict(sha256=h) for d,h in c['complete_direct_fingerprint'].items()})
 else:raise RuntimeError('No accepted object for '+m)
code='''import json,pathlib,hashlib,sys
rows=json.load(sys.stdin);H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');env=json.load(open(H/'J.json'));roots=[pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));assert all(v==base.get(k) for k,v in env.items() if k!='LEAN_PATH')
actual={};fail=[]
for m,x in rows.items():
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).is_file()),None)
 assert p is not None,m
 a=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),authority=x['authority']);actual[m]=a
 if 'object_sha256' in x and a['sha256']!=x['object_sha256']:fail.append([m,'object mismatch'])
 if 'source_sha256' in x:
  s=H/'sources'/(m.replace('.','/')+'.lean');a['source_sha256']=hashlib.sha256(s.read_bytes()).hexdigest()
  if a['source_sha256']!=x['source_sha256']:fail.append([m,'source mismatch'])
for m,x in rows.items():
 for d,v in x.get('dependencies',{}).items():
  if actual[d]['sha256']!=v['sha256']:fail.append([m,d,'dependency mismatch'])
print(json.dumps(dict(toolchain_match=True,objects=actual,failures=fail,all_match=not fail)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(expect),text=True,capture_output=True)
assert p.returncode==0,p.stderr
out=json.loads(p.stdout);out['roots']=roots;out['resolved_source_authority_sha256']=hashlib.sha256((E/'focused-resolution.json').read_bytes()).hexdigest()
(E/'final-closure-check.json').write_text(json.dumps(out,indent=2)+'\n')
assert out['all_match'],out['failures'];print('Complete public/private import closure:',len(seen),'objects; all source/object/direct fingerprints match; toolchain matches')
