from pathlib import Path
import json,hashlib,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];passed={};errors=[]
for p in sorted(E.glob('FIs_[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert '-M7000' in r['command'] and r['swaps']=='0',p
 for line in (r['print_axioms'] if r['exit_status']==0 else []):
  if 'depends on axioms:' in line:
   axs=line.split('depends on axioms:')[1].strip().strip('[]').split(', ')
   assert set(axs)<={'propext','Classical.choice','Quot.sound',''},line
 if r['exit_status']==0:
  for n,h in r['source_hashes'].items():passed.setdefault(n,[]).append((h,r['attempt']))
 else:errors.append(dict(attempt=r['attempt'],source=r['sources'],exit=r['exit_status']))
files={}
for p in sorted((R/'lean').glob('FIs_*.lean')):
 s=p.read_text(); assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',s),p
 h=sha(p);hits=[a for v,a in passed.get(p.name,[]) if v==h]
 files[p.name]=dict(sha256=h,passing_attempts=hits)
missing=[n for n,d in files.items() if not d['passing_attempts']]
out=dict(attempts=len(receipts),kani_runs=0,failures=errors,files=files,missing=missing,all_current_sources_pass=not missing,scope='focused new-prefix composition and atomic inventories, no package or frozen manifest replay')
(E/'FIs_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['attempts','failures','missing','all_current_sources_pass']},indent=2))
if '--final' in sys.argv:assert len(receipts)==100 and not missing
