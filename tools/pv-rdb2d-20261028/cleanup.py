from pathlib import Path
import hashlib,json,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
r=json.loads((D/'rdb2d-final-replay-receipt.json').read_text());o=D/'lean-objects/R1Z/PV_RDB2D_FinalReplay.olean';s=D/'lean-sources/R1Z/PV_RDB2D_FinalReplay.lean';assert sha(s)==r['source_sha256']
replay=dict(module=r['module'],source_revision=r['source_revision'],source_sha256=sha(s),object_sha256=sha(o),object_bytes=o.stat().st_size,imports=[])
for m in ['PV_RDB2D_StatementAudit','PV_RDB2D_AxiomsAudit']:
 p=D/'lean-objects/R1Z'/(m+'.olean');replay['imports'].append(dict(module='R1Z/'+m,object_sha256=sha(p)))
(D/'rdb2d-final-replay-object.json').write_text(json.dumps(replay,indent=2))
removed=[]
for name in ['lean-objects','target-weights']:
 p=D/name;assert p.resolve().is_relative_to(D.resolve()) and p.is_dir()
 files=[x for x in p.rglob('*')if x.is_file()];candidates=[str(x)for x in files if 'keypair' in x.name.lower()or x.name in ['id.json','wallet.json']or x.suffix=='.key'];assert not candidates,candidates
 binaries=[]
 for x in files:
  if x.parent==D/'target-weights/release' and x.stat().st_mode&0o111:
   binaries.append(dict(path=str(x),sha256=sha(x),bytes=x.stat().st_size))
 record=dict(path=str(p),files=len(files),bytes=sum(x.stat().st_size for x in files),binary_hashes=binaries,wallet_key_candidates=candidates)
 shutil.rmtree(p);record['removed']=not p.exists();removed.append(record)
j=dict(removed=removed,retained='all source, raw receipts, standard-library snapshots, canonical source authorities, complete dependency fingerprints and final replay object metadata; no other job directory touched',wallet_or_account_keys_created_accessed_removed=False)
(D/'rdb2d-cleanup.json').write_text(json.dumps(j,indent=2));print(json.dumps(j),flush=True)
