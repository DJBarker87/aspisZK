"""One-line local progress; no launch, retry or host access."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
files=sorted((E/'NMC_audit').glob('proof*/proof*.json'))
roots=[];rss=[];disagree=[];nonstandard=[]
for p in files:
 x=json.loads(p.read_text());rss.append(int(x['peak_rss_kib']))
 for r in x['results']:
  roots.append(r['root'])
  if not r['equal']:disagree.append(r['root'])
  if not set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}:nonstandard.append(r['root'])
receipts=list(E.glob('NMC_L*/receipt.json'))
print(json.dumps(dict(raw_groups=len(files),roots=len(roots),duplicate_roots=len(roots)-len(set(roots)),peak_rss_kib=max(rss,default=0),collector_disagreements=disagree,nonstandard=nonstandard,lean_support_receipts=len(receipts),close_received=(E/'NMC_L140/receipt.json').exists(),client_active=(E/'NMC_CLIENT_ACTIVE').exists())))
