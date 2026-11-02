"""Read-only verification of task copies against NDR and their original cache."""
import hashlib,json,lzma
from pathlib import Path
B=Path(__file__).resolve().parent
S=Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects')
D=B/'objects'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
pins=json.loads((B/'NDR_FINAL_COHORT_PINS.json').read_text()); checks=[]
for row in pins['entries']:
 rel=Path(row['module'].replace('.','/')+'.olean')
 got=sha(D/rel)
 assert got==row['object_sha256'],str(rel)
 checks.append({'path':str(rel),'sha256':got,'ndr_pin':True})
# Every copied object and split companion: source and copy must be byte-identical.
for src in sorted(S.rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(S);orig=sha(src);got=sha(D/rel)
 assert orig==got,str(rel)
 checks.append({'path':str(rel),'sha256':got,'copy_equals_read_only_seed':True,'bytes':src.stat().st_size})
lead=Path('/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027')
runners={name:sha(lead/name) for name in ['reservation_agg16.py','S2W_lean_host_agg16.py','S2W_run_host_agg16.py']}
for name,digest in runners.items():assert sha(B/name)==digest
result={'valid':True,'ndr_module_count':len(pins['entries']),'checks':checks,'lead_owned_runners':runners,'seed':str(S),'copy':str(D),'ndr_manifest_sha256':sha(B/'NDR_FINAL_COHORT_PINS.json')}
raw=(json.dumps(result,indent=2)+'\n').encode();(B/'NEP_CACHE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NEP_CACHE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps({'valid':True,'ndr_modules':len(pins['entries']),'checks':len(checks),'lead_owned_runners':runners}))
