from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
rows=[]
p=E.parent/'claims2-20261108'
for m in json.loads((p/'NKA_MODULES.json').read_text()):
 rc=json.loads(raw(p/m['attempt']/'receipt.json'));assert rc['exit_status']==0
 assert H(raw(p/m['source']))==m['sha256']and m['sha256']in rc['source_hashes'].values()
 rows.append(dict(provider='NKA',module=m['module'],attempt=m['attempt'],source=m['source'],sha256=m['sha256']))
p=E.parent/'poseidon-state-20261108'
for m,pin in json.loads((p/'NKG_PROOF_INVENTORY.json').read_text())['modules'].items():
 src='NKG_lean/'+m+'.lean';at=pin['attempt'];rc=json.loads(raw(p/at/'receipt.json'));assert rc['exit_status']==0
 h=H(raw(p/src));assert h==pin['source_sha256']and h in rc['source_hashes'].values()
 assert raw(p/src)==raw(p/at/'sources'/src)
 rows.append(dict(provider='NKG',module=m,attempt=at,source=src,sha256=h))
p=E.parent/'field4-20261108';compiled={}
for path in sorted(p.glob('NKJ_L[0-9][0-9][0-9]/receipt.json')):
 rc=json.loads(path.read_text())
 if rc['kind']=='lean'and rc['exit_status']==0:
  for n,h in rc['source_hashes'].items():
   if n.endswith('.lean'):compiled[n]=(h,rc['attempt'])
for n,(h,at)in compiled.items():
 assert H(raw(p/n))==h,(n,'changed after compilation')
 rows.append(dict(provider='NKJ',module=Path(n).stem,attempt=at,source=n,sha256=h))
(E/'NKN_SOURCE_PINS.json').write_text(json.dumps(dict(status='PASS',sources=rows,modules=len(rows),candidate_source_receipts_consistent=True),indent=1)+'\n')
print(json.dumps(dict(status='PASS',candidate_source_snapshots=len(rows))))
