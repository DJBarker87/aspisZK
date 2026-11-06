from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'NKR_ATTEMPTS.jsonl').read_text().splitlines()]
modules={p.stem:p for p in E.glob('NKR_*.lean') if p.stem not in ['NKR_Inventory','NKR_COMBINED_IMPORT','NKR_Driver','NKR_ProofDriver']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
passed={};latest={}
for r in attempts:
 if r.get('kind')!='lean':continue
 m=r['module'];latest[m]=r
 if r['exit_status']==0 and m in modules and r['source_hashes'].get(m+'.lean')==sha(modules[m]):passed[m]=r
pending=set(modules)-set(passed)
unchanged_fail={m for m in pending if m in latest and latest[m]['source_hashes'].get(m+'.lean')==sha(modules[m])}
# Never resubmit an unchanged failure: writing/repair remains necessary.
pending-=unchanged_fail
ordered=[];done=set(passed)
while pending:
 ready=sorted(m for m in pending if set(re.findall(r'^import (NKR_[\w.]+)',modules[m].read_text(),re.M))<=done)
 if not ready:break
 for m in ready:ordered.append(m);done.add(m);pending.remove(m)
start=int(sys.argv[1]);rows=[[f'NKR_L{i:03d}',m,[]] for i,m in enumerate(ordered,start)]
(E/'NKR_PENDING_QUEUE.json').write_text(json.dumps(rows))
(E/'NKR_PENDING_BLOCKS.json').write_text(json.dumps(dict(unchanged_failed=sorted(unchanged_fail),blocked=sorted(pending),queued=ordered)))
print('Focused queue: '+str(len(rows))+' modules; blocked '+str(len(pending))+'; unchanged failures excluded '+str(len(unchanged_fail)))
