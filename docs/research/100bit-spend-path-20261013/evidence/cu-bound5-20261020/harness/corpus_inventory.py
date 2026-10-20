import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]);out=[]
for name in ['control','variants','variants-extra','targeted','random-a','random-b']:
 p=json.loads((H/f'plan-{name}.json').read_text())
 for r in p['runs']:
  d=json.loads((H/f'sweep/{name}/runs'/r['label']/'evidence.json').read_text());f=d['fixture'];i=r['args'].index('--reuse');proof,public=map(Path,r['args'][i+1:i+3]);sha=hashlib.sha256(proof.read_bytes()).hexdigest();assert sha==f['proof_sha256']==f['submitted_proof_sha256']
  original=proof.parent.parent/'evidence.json';generation=None
  if name!='control':
   old=json.loads(original.read_text());assert old['fixture']['proof_sha256']==sha;generation=old['fixture']['mask_entropy_option'];assert generation=='os';assert old['fixture']['mask_mode']=='full-mask'
  out.append(dict(label=r['label'],source_proof=str(proof),proof_sha256=sha,proof_bytes=proof.stat().st_size,public_sha256=hashlib.sha256(public.read_bytes()).hexdigest(),source_mask_mode=generation or 'saved freeze control',measured_proof_identical=True))
(H/'corpus-inventory.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in out));print(len(out),'proof/public pins; exact prior random corpus OS masks verified')
