from pathlib import Path
import json,re,hashlib,subprocess
packet=Path(__file__).resolve().parent; root=packet.parents[1]
standard={'propext','Classical.choice','Quot.sound'}
receipts=[]
for f in sorted((packet/'receipts').glob('*/receipt.json')):
 r=json.loads(f.read_text()); log=(f.parent/'out.log').read_text()
 used=set()
 for line in r['axioms']:
  m=re.search(r'axioms: \[(.*)\]',line)
  if m: used.update(x.strip() for x in m[1].split(',') if x.strip())
 r['axioms_used']=sorted(used);r['standard_axioms_only']=used<=standard
 r['accepted']=r['exit']==0 and r['standard_axioms_only']
 if not r['accepted']:r['rejection_reason']='compiler error' if r['exit'] else 'nonstandard axiom: '+', '.join(sorted(used-standard))
 tm=r['time_log']
 for field,pattern in [('peak_rss_bytes',r'(\d+)\s+maximum resident set size'),('process_swaps',r'(\d+)\s+swaps')]:
  m=re.search(pattern,tm);r[field]=int(m[1]) if m else None
 m=re.search(r'([\d.]+) real',tm);r['timed_wall_seconds']=float(m[1]) if m else None
 r['receipt']=str(f.relative_to(root));f.write_text(json.dumps(r,indent=2)+'\n');receipts.append(r)
final=[]
for mod in ['R22Stage2LocalBodies','R22Stage2ControlBounds','R22Stage2LeafTotal','R22Stage2ReaderTotal','R22Stage2OpeningTotal','R22Stage2Audit']:
 src=root/'lean'/f'{mod}.lean';h=hashlib.sha256(src.read_bytes()).hexdigest()
 matches=[r for r in receipts if r['module']==mod and r['source_sha256']==h and r['accepted']]
 assert matches,mod
 r=matches[-1];final.append({k:r[k] for k in ['module','source_revision','source_sha256','exit','timed_wall_seconds','peak_rss_bytes','process_swaps','standard_axioms_only','receipt']})
audit=[r for r in receipts if r['module']=='R22Stage2Audit' and r['accepted']][-1]
assert len(audit['axioms'])==39
manifest={'schema':'focused-extractor-proof-packet-v1','scope':'focused stage2 arithmetic/range packet; not complete R22 or release replay','final_targets':final,'public_theorems_audited':39,'attempts':receipts}
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
index=[]
for f in sorted((root/'lean').glob('R22Stage2*.lean')):
 s=f.read_text();nm=re.search(r'^namespace (\S+)',s,re.M)
 if not nm:continue
 for m in re.finditer(r'^theorem (\w+)',s,re.M):
  index.append({'name':nm[1]+'.'+m[1],'source':str(f.relative_to(root)),'line':s[:m.start()].count('\n')+1})
(packet/'theorem-index.json').write_text(json.dumps(index,indent=2)+'\n')
assert len(index)==39
print(json.dumps(final,indent=2))
