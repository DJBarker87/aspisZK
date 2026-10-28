"""Keep the admission decision and raw byte hash without per-attempt inventories."""
from pathlib import Path
import json,hashlib,sys
E=Path(__file__).resolve().parents[2]/'evidence/pv-world-20261028'
def archive(n):
 for p in [E/f'upload-{n}.json',*(E/f'lean-{n}').glob('*')]:
  if p.name=='receipt.json':continue
  raw=p.read_bytes()
  if p.suffix=='.json':
   j=json.loads(raw)
   if 'sha256' not in j:j=dict(sha256=hashlib.sha256(raw).hexdigest(),**{k:j.get(k) for k in ['allowed','utc','error','bounded_reserved_bytes','safe_limit_bytes']})
   raw=(json.dumps(j,indent=2)+'\n').encode()
  (E/f'refusal-{n}-{p.name}').write_bytes(raw)
if __name__=='__main__':archive(int(sys.argv[1]))
