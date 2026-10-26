from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1];receipts=[]
for f in sorted(P.glob('FIq_[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(f.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},f
 assert '-M7000' in x['command'] and x['swaps']=='0',f
 receipts.append(x)
current={}
for f in sorted((R/'lean').glob('FIq_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest();matches=[x for x in receipts if x['exit_status']==0 and x['source_hashes'].get(f.name)==sha]
 code=re.sub(r'/--.*?-/|/-.*?-/', '',f.read_text(),flags=re.S)
 assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b|set_option max(?:Heartbeats|RecDepth)',code),f
 current[f.name]=dict(sha256=sha,successful_attempts=[x['attempt'] for x in matches])
for x in receipts:
 if x['exit_status']==0:
  for report in x['print_axioms']:
   if 'depends on axioms:' not in report:continue
   axioms=re.search(r'\[([^]]*)\]',report,re.S)[1].replace('\n','').split(',')
   assert set(a.strip() for a in axioms)<=set(['propext','Classical.choice','Quot.sound']),x['attempt']
# Only successful receipts are acceptable evidence; failed source snapshots are
# deliberately retained, including the rejected postulate/namespace audits.
base='fc86a9e5b7'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/FIq_') or p.startswith('evidence/finish-install4-20261026/') for p in changed)
preflights=[json.loads(f.read_text()) for f in P.glob('FIq_[0-9][0-9][0-9]-preflight.json')]
out=dict(lean_attempts=len(receipts)+len(preflights),compiler_starts=len(receipts),preflights=preflights,kani_runs=0,passed=sum(x['exit_status']==0 for x in receipts),failed=[dict(attempt=x['attempt'],target=x['sources'],exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps']) for x in receipts if x['exit_status']!=0],current_sources=current,unvalidated_current=[n for n,x in current.items() if not x['successful_attempts']],caps_verified=True,accepted_axioms_standard=True,scope='Focused new-module checks against coherent SInt2/cache selection; not a release replay',baseline=base)
(P/'FIq_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['lean_attempts','passed','failed','unvalidated_current','caps_verified','accepted_axioms_standard']},indent=2))
