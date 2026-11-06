"""Remove only NJW rebuildable scratch after verifying the retained export."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger16-20261108'
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(B);x=json.loads((b/'NJW_EXPORT.json').read_text());checked=[]
for r in x['files']:
 p=Path(r['path']);assert p.is_file()and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];checked.append(str(p))
assert checked
removed=[]
for n in ['NJW_objects','NJW_native','NJW_tmp']:
 p=b/n
 if p.exists():
  assert p.parent==b and not p.is_symlink();size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
out=dict(export_hashes_verified=len(checked),export=x['export'],export_bytes=x['bytes'],retained_cache='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJW_20261108',cache_deleted=False,removed=removed,source_and_receipts_retained=True,CARGO_TARGET_DIR=str(b/'NJW_target'),CARGO_TARGET_DIR_exists=(b/'NJW_target').exists(),disk=shutil.disk_usage(b)._asdict())
(b/'NJW_HOST_END.json').write_text(json.dumps(out,indent=1));print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\n'+code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NJW_HOST_END.json').write_text(r.stdout);print(json.dumps(dict(stage='cleanup',cache_retained=True,removed_bytes=sum(x['bytes']for x in json.loads(r.stdout)['removed']))))
