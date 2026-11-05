from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
inputs=json.loads((R/'evidence/inv-repair-20261104/NGB_MIR_EDGES.json').read_text())['inputs'];out=[]
for item in inputs:
 p=R/item['path'];raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==item['sha256'];text=lzma.decompress(raw).decode();lines=text.splitlines();fn='';hits=[]
 for i,l in enumerate(lines):
  if l.startswith('fn '):fn=l
  if any(k in l for k in ['CM31::inv_with(', 'cm31_batch_inverse_with(', 'cm31_batch_inverse(']):hits.append(dict(line=i+1,function=fn,context='\n'.join(lines[max(0,i-4):i+3])))
 out.append(dict(input=item,hits=hits))
# The authoritative union and transaction rows, without changing membership.
ledger=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
(E/'NHN_CENSUS.json').write_text(json.dumps(out,indent=2)+'\n')
for x in out:
 print(x['input']['path'])
 for h in x['hits']: print(h['function'],h['context'])

# Read-only adopted inventory coverage is retained separately in NHN_INSTANTIATION_COVERAGE.json.
