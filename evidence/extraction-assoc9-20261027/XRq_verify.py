from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rows=[];errors=[];latest={}
for p in sorted(E.glob('XRq_L*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append(a+' not admitted')
 # The barrier log and launch receipt retain exit0 + allowed:true admission.
 if not r['sources'] or '-M7000' not in r['command']:errors.append(a+' scope command')
 if str(r['swaps'])!='0':errors.append(a+' swaps')
 for src,sha in r['source_hashes'].items():
  f=p.parent/'sources'/src
  if not f.exists() or hashlib.sha256(f.read_bytes()).hexdigest()!=sha:errors.append(a+' source snapshot')
 if r['exit_status']==0:
  if any('sorryAx' in line for line in r['print_axioms']):errors.append(a+' nonstandard axioms')
  latest[r['module']]=(a,r)
 rows.append(r)
assert len(rows)<=100
for m,(a,r) in latest.items():
 f=E/(m+'.lean')
 if m.startswith('XRq_') and f.exists():
  if hashlib.sha256(f.read_bytes()).hexdigest() not in r['source_hashes'].values():errors.append(m+' final source differs from accepted receipt')
x=dict(errors=errors,compiler_runs=len(rows),passes=sum(r['exit_status']==0 for r in rows),failures=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),kani_runs=0,latest_accepted={m:a for m,(a,r) in latest.items()},new_axioms={m:r['print_axioms'] for m,(a,r) in latest.items() if m.startswith('XRq_')})
(E/'XRq_VERIFICATION.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'XRq_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
print(json.dumps({k:v for k,v in x.items() if k not in ['latest_accepted','new_axioms']}))
