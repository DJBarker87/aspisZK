"""Read-only audit of retained proof/admission/source receipts."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];errors=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
transport=[json.loads(s) for s in (E/'XSe_transport.jsonl').read_text().splitlines()]
for i in range(1,101):
 a=f'XSe_L{i:03d}';r=json.loads((E/a/'receipt.json').read_text());receipts.append(r)
 if r['limits']!=limits:errors.append([a,'caps'])
 for src,h in r['source_hashes'].items():
  if sha(E/a/'sources'/src)!=h:errors.append([a,'snapshot',src])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'admission'])
 barrier=[t for t in transport if 'S2H_reservation.py' in ' '.join(t['argv']) and a+'-reservation.json' in ' '.join(t['argv'])]
 if not barrier or barrier[-1]['exit']!=0:errors.append([a,'admission_exit'])
 if '-M7000' not in r['command']:errors.append([a,'lean_memory'])
 if r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^]]*)\]',line)
   if m and set(s.strip() for s in m[1].split(',') if s.strip())-{'propext','Classical.choice','Quot.sound'}:errors.append([a,'axioms',line])
sel=json.loads((E/'XSe_AUDIT_SELECTION.json').read_text())
for s in sel['modules']:
 f=E/(s['module']+'.lean');r=json.loads((E/s['receipt']/'receipt.json').read_text())
 if r['source_hashes'].get('XSe_generated/'+f.name)!=sha(f):errors.append([s['module'],'final_source'])
start=json.loads((E/'XSe_cache_START.json').read_text());end=json.loads((E/'XSe_cache_END.json').read_text())
changed=[k for k,v in start.items() if end.get(k)!=v]
if changed:errors.append(['cache','changed_start_objects',changed])
if sha(E/'XSe_top_before.lean.txt')!=sha(E/'XSe_top_after.lean.txt'):errors.append(['headline_changed'])
summary={'attempts':len(receipts),'passed':sum(r['exit_status']==0 for r in receipts),'failed':sum(r['exit_status']!=0 for r in receipts),'kani_runs':0,'compiler_wall_seconds':sum(r['wall_seconds'] for r in receipts),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':sum(int(r['swaps']) for r in receipts),'final_audit':{k:receipts[-1][k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']},'new_theorems_audited':len(sel['new_theorems']),'cache':{'retained':True,'start_count':len(start),'end_count':len(end),'start_objects_changed':changed,'end_bytes':sum(x['size'] for x in end.values())},'headline_sha256':sha(E/'XSe_top_before.lean.txt'),'errors':errors}
(E/'XSe_attempts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in receipts))
(E/'XSe_FINAL_CHECKS.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
assert not errors
