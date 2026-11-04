"""Recover overwritten preparation INPUTS, accepting only the original digest.
No compile is repeated and no historical observation is invented: the original
receipt's SHA-256 must match the deterministic reconstruction byte for byte.
"""
from pathlib import Path
import json,hashlib,subprocess
E=Path('evidence/pv-stx-20261104');H='/home/dombarker/project-offloads/codex-pv-stx-20261104'
base=json.loads(Path('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json').read_text())['result']
rs=sorted((json.loads(p.read_text()) for p in E.glob('receipt-*.json')),key=lambda r:r['attempt'])
archive=E/'preparations';archive.mkdir(exist_ok=True);snapshots={}
for p in list(E.glob('prepare-*.json'))+list((E/'prepare-history').glob('*.json')):
 snapshots[hashlib.sha256(p.read_bytes()).hexdigest()]=p.read_bytes()
ref=json.loads((E/'prepare-PV_STX_Code.json').read_text())['result']
paths={v['module']:v['path'] for v in ref['effective_resolution']}
old_order=[v['module'] for v in json.loads((E/'prepare-PV_STX_DenoteRules.json').read_text())['result']['project_dependencies'] if v['module'].startswith('PV_STX_')]
recovered=[];missing=[]
for r in rs:
 fp=r['deps_fingerprint'];raw=snapshots.get(fp);method='preserved original'
 if raw is None:
  prior=[q for q in rs if q['attempt']<r['attempt'] and q['accepted']]
  if r['attempt']>=91716:
   latest={}
   for q in prior:
    p='lean/'+q['target']+'.lean'
    s=subprocess.run(['git','show',r['source_revision']+':'+p],capture_output=True).stdout
    if hashlib.sha256(s).hexdigest()==q['source_sha256']:latest[q['target']]=q
   prior=list(latest.values())
  if r['attempt']<91716:prior.sort(key=lambda q:old_order.index(q['target']))
  checks=base['project_checks']+[dict(module=q['target'],sha256=q['object_sha256'],path=H+'/objects/'+q['target']+'.olean') for q in prior]
  effective=[dict(module=v['module'],path=paths.get(v['module'],v['path']),sha256=v['sha256']) for v in base['external_checks']+checks]
  result=dict(source_sha256=r['source_sha256'],source_revision=r['source_revision'],toolchain=base['toolchain'],LEAN_PATH=H+'/objects:'+base['LEAN_PATH'],effective_resolution=effective,external_authority='h4 pv-replay-20261027 (inherited verified evh4 manifest)',project_dependencies=checks,shared_written=False)
  raw=(json.dumps(dict(exit=0,stderr='',result=result),indent=2)+'\n').encode();method='deterministic reconstruction, original digest verified'
 if hashlib.sha256(raw).hexdigest()!=fp:missing.append(r['attempt']);continue
 p=archive/(str(r['attempt'])+'.json');p.write_bytes(raw);recovered.append(dict(attempt=r['attempt'],sha256=fp,path=str(p),method=method))
(E/'preparations/recovery.json').write_text(json.dumps(dict(recovered=recovered,missing=missing),indent=2)+'\n')
assert not missing,missing
print('retained',len(recovered),'exact preparation inputs')
