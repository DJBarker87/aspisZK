"""Read-only revalidation of every reused selected native pair; no prover replay."""
from pathlib import Path
import json,hashlib,re,lzma
E=Path(__file__).resolve().parent;P=E.parent/'transcript-queries-20261105';B=E.parent/'transcript-queries2-20261105'
pairs=[(P,r['positive'],r['negative']) for r in json.loads((P/'NGQ_NATIVE_RESULTS.json').read_text())['selected']]
for r in json.loads((E/'NHK_MEMBERSHIP_CALLEES.json').read_text())['cases']:
 if r['positive'].startswith('NHB_'):pairs.append((B,r['positive'],r['control']))
for p,n in [(30,31),(43,44),(50,51),(53,54)]:pairs.append((B,f'NHB_K{p:03}',f'NHB_K{n:03}'))
frozen=json.loads(lzma.decompress((P/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))
seen=set();rows=[]
for root,pos,neg in pairs:
 if (pos,neg) in seen:continue
 seen.add((pos,neg))
 for a,positive in [(pos,True),(neg,False)]:
  r=json.loads((root/a/'receipt.json').read_text());raw=(root/a/'stdout.log').read_text()
  assert r['exit_status']==(0 if positive else 1) and 'timed out' not in raw and 'CBMC failed' not in raw,a
  assert ('VERIFICATION:- SUCCESSFUL' in raw) if positive else ('Failed Checks:' in raw and re.search(r'\*\* 1 of \d+ failed',raw))
  assert json.loads((root/(a+'-graph-check.json')).read_text())['graph_matches_frozen'],a
  assert json.loads((root/(a+'-lock-check.json')).read_text())['unchanged'],a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and str(r['swaps'])=='0'
  ad=json.loads((root/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
  for name,h in r['source_hashes'].items():
   p=root/a/'sources'/name
   if p.exists():data=p.read_bytes()
   else:
    rel=name.split('_src/',1)[1];assert rel in frozen,(a,name)
    data=frozen[rel].encode()
   assert hashlib.sha256(data).hexdigest()==h,(a,name)
 rows.append(dict(positive=pos,control=neg,status='REVALIDATED_WITHOUT_REPLAY',positive_receipt_sha256=hashlib.sha256((root/pos/'receipt.json').read_bytes()).hexdigest(),control_receipt_sha256=hashlib.sha256((root/neg/'receipt.json').read_bytes()).hexdigest()))
(E/'NHK_REVALIDATED_REUSE.json').write_text(json.dumps(dict(status='PASS',pairs=len(rows),new_tool_attempts=0,results=rows),indent=2)+'\n');print(json.dumps(dict(status='PASS',pairs=len(rows),new_tool_attempts=0)))
