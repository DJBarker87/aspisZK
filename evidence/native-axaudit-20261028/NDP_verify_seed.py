"""Read-only verification of every COPIED seed artifact against predecessor pins."""
import hashlib,json,time
from pathlib import Path
B=Path(__file__).resolve().parent
S='/home/dombarker/project-offloads/codex-cx-l188-cache-20261028'
p=B/'NDJ_CACHE_PINS.json';raw=p.read_bytes();x=json.loads(raw)
start=time.monotonic();count=total=0
for row in x['objects']:
 for item in row['artifacts']:
  q=Path(item['path'].replace(S,str(B)))
  h=hashlib.sha256()
  with q.open('rb') as f:
   for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
  assert q.stat().st_size==item['bytes'] and h.hexdigest()==item['sha256'],str(q)
  count+=1;total+=q.stat().st_size
out=dict(seed=S,copy=str(B),seed_manifest_sha256=hashlib.sha256(raw).hexdigest(),artifacts_verified=count,bytes_verified=total,wall_seconds=time.monotonic()-start,comparison='Every copied .olean, .olean.private, .olean.server and .ir listed in the unchanged NDJ manifest has identical SHA256 and size',original_seed_access='read-only COPY; never modified',retention='Own cache retained')
(B/'NDP_SEED_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
