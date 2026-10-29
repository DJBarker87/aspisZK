from pathlib import Path
import json,hashlib,subprocess,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag9-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(D/'final_check.py'),'--post'],check=True)
receipts=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))];assert [r['attempt'] for r in receipts]==list(range(66200,66300))
failed=set();latest={}
for r in receipts:
 assert r['source_sha256'] not in failed,'unchanged failed source resubmitted'
 if r['exit']!=0:failed.add(r['source_sha256'])
 else:latest[r['module']]=r
plans=json.loads((D/'plans.json').read_text());identity=[]
for m,r in latest.items():
 p=D/'sources'/(m+'.lean');assert sha(p)==r['source_sha256']
 if m in plans:assert hashlib.sha256(plans[m][-1].encode()).hexdigest()==sha(p),m
 identity.append(dict(module=m,sha256=sha(p),accepted_attempt=r['attempt'],object_sha256=r['object_sha256']))
newnames=set()
for m in plans:
 for n in re.findall(r'^#print axioms (\S+)',(D/'sources'/(m+'.lean')).read_text(),re.M):newnames.add('PV_DIAG9.'+n)
auditnames=set()
for n in [66297,66298,66299]:auditnames.update(re.findall(r"'([^']+)'",(D/('lean'+str(n)+'-output.log')).read_text()))
assert newnames<=auditnames,newnames-auditnames
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(Path(r['path']))==r['object_sha256']
summary=dict(lean_attempts=len(receipts),accepted=sum(r['exit']==0 for r in receipts),rejected=[r['attempt'] for r in receipts if r['exit']!=0],new_names_audited=len(newnames),external_objects_checked=len(ext),sources=identity,resource_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),max_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_scope_wall_seconds=sum(r['wall_seconds'] for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),audits=[{k:r[k] for k in ['attempt','module','exit','gnu_wall','wall_seconds','peak_rss_kib','swaps','source_revision','source_sha256','print_axioms']} for r in receipts if r['attempt']>=66297],final_check_sha256=sha(D/'final_check.py'))
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
# Only this job's private compiler products; no referenced object/key is touched.
removed=[]
for p in (D/'objects').rglob('*'):
 if p.is_file() and not p.is_symlink():
  assert p.name.startswith('PV_DIAG9_'),str(p)
  removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(removed=removed,retained='all source snapshots, receipts and read-only shared cache links; no keys or funds created/touched'),indent=2)+'\n')
print('Lean',len(receipts),'accepted',summary['accepted'],'rejected',len(summary['rejected']),'audited names',len(newnames),'external',len(ext),'private products removed',len(removed))
