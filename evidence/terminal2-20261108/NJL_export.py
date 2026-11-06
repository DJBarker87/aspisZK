"""Post-audit own-artifact retention and own rebuildable-scratch cleanup; no build."""
from pathlib import Path
import json,hashlib,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-terminal2-20261108')
R=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJL_20261108')
D=R/'NJL_exports_20261108'
assert not D.exists(),'Recover read-only; never overwrite a retained export'
for a in['NJL_L200','NJL_L201','NJL_L202','NJL_L203']:
 assert json.loads((B/a/'receipt.json').read_text())['exit_status']==0,a
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NJL_GATE_SOURCES.json').read_text());modules=sorted(x['passed'])+['NJL_COMBINED_IMPORT']
for row in x['source_extensions']:
 assert sha(B/(row['module']+'.lean'))==row['sha256'],row['module']
for m in modules:assert (B/'NJL_objects'/(m+'.olean')).is_file(),m
before=shutil.disk_usage(B).free
R.mkdir(parents=True,exist_ok=True,mode=0o700)
shutil.move(str(B/'NJL_objects'),str(D))
for m in modules:shutil.copyfile(B/(m+'.lean'),D/(m+'.lean'))
for n in['NJL_seed','NJL_NIX_seed','NJL_native']:
 dest=R/('NJL_audit_native'if n=='NJL_native'else n)
 assert not dest.exists();shutil.move(str(B/n),str(dest))
for name in['NJL_Driver','NJL_ProofDriver']:
 old=next(r for r in json.loads((B/'NJL_LINK.json').read_text())if r['target']==name)
 assert sha(R/'NJL_audit_native'/name)==old['sha256']
# Never remove a possible wallet/account key. No such keys are expected in a
# cargo-kani-only target or own solver directory; retain either if discovered.
cleanup=[]
for name in['NJL_target','NJL_tmp']:
 p=B/name
 if not p.exists():continue
 keys=[str(q)for q in p.rglob('*')if q.is_file()and(q.suffix in['.key','.pem']or q.name.startswith('id_ed')or ('keypair'in q.name.lower()and q.suffix in['.json','.bin'])or ('wallet'in q.name.lower()and q.suffix=='.json'))]
 if keys:cleanup.append(dict(path=str(p),removed=False,reason='Potential key material retained',potential_keys=keys));continue
 shutil.rmtree(p);cleanup.append(dict(path=str(p),removed=True,potential_keys=[]))
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file():files.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
seeds=[]
for name in['NJL_seed','NJL_NIX_seed']:
 for p in sorted((R/name).rglob('*')):
  if p.is_file():seeds.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
config=json.loads((B/'NJL_L203.json').read_text());lean_path=config['env']['LEAN_PATH'].replace(str(B/'NJL_objects'),str(D)).replace(str(B/'NJL_seed'),str(R/'NJL_seed')).replace(str(B/'NJL_NIX_seed'),str(R/'NJL_NIX_seed'))
out=dict(status='RETAINED_AFTER_GATE2_PASS',source_revision=config['source_revision'],export_dir=str(D),modules=modules,files=files,total_bytes=sum(r['bytes']for r in files),seed_files=seeds,seed_bytes=sum(r['bytes']for r in seeds),lean_path=lean_path,aeneas_pins='NJL_L203/receipt.json deps_fingerprint.selected_objects (unchanged retained read-only library objects)',audit_native=str(R/'NJL_audit_native'),cleanup=cleanup,free_before=before,free_after=shutil.disk_usage(B).free,note='Own objects/seeds/native audit artifacts moved into retained OWN cache, never deleted; only own rebuildable cargo/solver scratch removed after potential-key filename check. No key cleanup performed.')
raw=json.dumps(out,indent=2)+'\n';(R/'NJL_EXPORT.json').write_text(raw);(B/'NJL_EXPORT.json').write_text(raw);print(raw)
