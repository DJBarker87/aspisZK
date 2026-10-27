"""Read-only source/receipt checks. No prover or build is launched."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
errors=[]
sha=lambda b:hashlib.sha256(b).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
lean=[];kani=[]
for p in sorted(E.glob('LPb_[LK]*/receipt.json')):
 d=json.loads(p.read_text());(lean if d['kind']=='lean' else kani).append(d)
 for f,h in d['source_hashes'].items():
  q=p.parent/'sources'/f
  if not q.is_file() or sha(q.read_bytes())!=h:errors.append('input hash '+str(q))
 if d['limits']!=limits:errors.append('caps '+d['attempt'])
 for k in ['command','source_revision','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','exit_status','print_axioms']:
  if k not in d:errors.append('missing '+k+' '+d['attempt'])
 if int(d['swaps']):errors.append('swap '+d['attempt'])
 if d['kind']=='lean' and d['exit_status']==0:
  for line in d['print_axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',line)
   if m and not {x.strip() for x in m[1].split(',') if x.strip()}<=allowed:errors.append('nonstandard '+line)
 if d['reservation_retries']!=0:errors.append('inspect admission retry '+d['attempt'])
latest={}
for d in lean:
 if d['exit_status']==0:latest[d['module']]=d
for p in sorted(E.glob('LPb_*.lean')):
 d=latest.get(p.stem)
 if not d or sha(p.read_bytes()) not in d['source_hashes'].values():errors.append('no current green source '+p.name)
 s=p.read_text()
 if 'set_option autoImplicit false' not in s:errors.append('implicit creation enabled '+p.name)
 if re.search(r'^\s*(axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M):errors.append('forbidden source '+p.name)
inventory=json.loads((E/'LPb_theorem_inventory.json').read_text())
audit=latest.get('LPb_Audit',{})
printed={re.match(r"'([^']+)'",line)[1] for line in audit.get('print_axioms',[])}
if printed!=set(inventory['theorems']):errors.append('final theorem audit inventory mismatch')
for n in inventory['theorems']:
 if '#check @'+n not in (E/'LPb_Audit.lean').read_text():errors.append('missing statement check '+n)
if len(kani)!=20 or len(lean)>60:errors.append('budget mismatch')
if [d['attempt'] for d in kani]!=[f'LPb_K{i:03}' for i in range(1,21)]:errors.append('Kani attempt gap')
if [d['attempt'] for d in lean]!=[f'LPb_L{i:03}' for i in range(1,len(lean)+1)]:errors.append('Lean attempt gap')
rec=json.loads((E/'LPb_recount.json').read_text())
b=(E/'LPb_Top.BEFORE.lean.txt').read_bytes();a=(E/'LPb_Top.AFTER.lean.txt').read_bytes()
if b!=a or sha(b)!=rec['before_sha256'] or sha(a)!=rec['after_sha256']:errors.append('top changed')
for f,h in rec['source_pins'].items():
 if sha(Path(f).read_bytes())!=h:errors.append('recount pin '+f)
changed=subprocess.check_output(['git','diff','--name-only','09fe80440d'],text=True).splitlines()
if any(not f.startswith('evidence/leaf-p6-2-20261027/') for f in changed):errors.append('out of scope tracked change')
summary={'errors':errors,'lean_used':len(lean),'lean_pass':sum(d['exit_status']==0 for d in lean),'lean_fail':sum(d['exit_status']!=0 for d in lean),'lean_wall_seconds':sum(d['wall_seconds'] for d in lean),'lean_peak_rss_kib':max(int(d['peak_rss_kib']) for d in lean),'lean_peak_cgroup_memory_bytes':max(int(d['cgroup_memory_peak_bytes']) for d in lean),'lean_swaps':sum(int(d['swaps']) for d in lean),'kani_used':len(kani),'audited_theorems':len(printed),'final_modules':len(latest),'standard_axioms_only_on_accepted_theorems':not any('nonstandard' in e for e in errors),'top_delta':rec['delta'],'current_module_receipts':{m:d['attempt'] for m,d in latest.items()}}
(E/'LPb_Verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2));raise SystemExit(bool(errors))
