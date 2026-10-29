"""Record final artifacts, then remove only this task's compiled scratch."""
from pathlib import Path
import json,hashlib,shutil,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2e-20261029')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fp=json.loads(lzma.decompress((D/'dependency-fingerprint.json.xz').read_bytes()))
for r in fp['objects']:assert sha(Path(r['path']))==r['object_sha256'],r['module']
audits=[]
for n,m in [(62297,'StatementAudit'),(62298,'AxiomsAudit'),(62299,'FocusedReplay')]:
 p=D/'lean-objects/R1Z'/('PV_RDB2E_'+m+'.olean');s=D/'lean-sources/R1Z'/('PV_RDB2E_'+m+'.lean')
 audits.append(dict(attempt=n,module='R1Z/PV_RDB2E_'+m,object_sha256=sha(p),object_bytes=p.stat().st_size,source_sha256=sha(s)))
(D/'final-audit-objects.json').write_text(json.dumps(audits,indent=2))
removed=[]
for name in ['target','lean-objects']:
 p=D/name;assert p.parent==D and p.name in ['target','lean-objects']
 files=[f for f in p.rglob('*')if f.is_file()]
 candidates=[str(f)for f in files if any(x in f.name.lower()for x in ['keypair','private-key','wallet-key','.pem'])]
 assert not candidates,dict(retained_key_candidates=candidates)
 rows=[dict(path=str(f.relative_to(D)),sha256=sha(f),bytes=f.stat().st_size)for f in files if f.suffix=='.olean']
 removed.append(dict(path=str(p),files=len(files),bytes=sum(f.stat().st_size for f in files),objects=rows,key_candidates=candidates))
 shutil.rmtree(p)
r=dict(removed=removed,final_audit_objects=audits,independent_model_object_hashes_unchanged=True,retained='source snapshots, pinned source and dependency manifests, native binary hash/size, raw receipts, uncredited drafts; no other job directory touched',wallet_or_account_keys_created_accessed_removed=False)
(D/'cleanup.json').write_text(json.dumps(r,indent=2));print(json.dumps(dict(removed=[{k:v for k,v in x.items()if k!='objects'}for x in removed],audits=audits,wallet_activity=False)),flush=True)
