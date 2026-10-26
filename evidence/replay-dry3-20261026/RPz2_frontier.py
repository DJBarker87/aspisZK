"""Evidence-only frontier and receipt consistency checks; no prover execution."""
from pathlib import Path
import json,collections,hashlib,subprocess
E=Path(__file__).resolve().parent;g=json.loads((E/'RPz2_source-plan.json').read_text());old=json.loads((E.parent/'replay-dry2-20261026/RPz_state.json').read_text());state={m:s for m,s in old['state'].items() if s in ['passed','failed']};receipts=[json.loads(f.read_text()) for f in sorted(E.glob('RPz2_*/receipt.json'))];sources=[r for r in receipts if not r['module'].startswith('RPz2_Audit')];provenance={};errors=[]
for r in sources:
 m=r['module'];state[m]='passed' if r['exit_status']==0 else 'failed';x=g['modules'][m]
 hashes=list(r['source_hashes'].values())
 if hashes!=[x['sha256']]:errors.append({'attempt':r['attempt'],'source_hash_mismatch':hashes})
 if 'snapshot' in x:
  path=x['snapshot'];revision=subprocess.check_output(['git','log','--diff-filter=A','--format=%H','--',path],text=True).splitlines()[0]
  data=subprocess.check_output(['git','show',revision+':'+path]);assert hashlib.sha256(data).hexdigest()==x['sha256']
  provenance[r['attempt']]={'source_snapshot_revision':revision,'source_snapshot_path':path,'source_sha256':x['sha256'],'receipt_source_revision':r['source_revision'],'qualification':'The committed replay snapshot revision supplies an exact source revision where the raw receipt names retained-host-source-snapshot. No historical source receipt is inferred.'}
failed=sorted(m for m,s in state.items() if s=='failed');ready=[]
for m in g['order']:
 if m not in state:
  state[m]='blocked'
  if all(g['modules'][n]['kind']=='trusted-library' or state.get(n)=='passed' for n in g['modules'][m]['imports']):ready.append(m)
q=collections.deque([['Rc7_Top']]);seen=set();paths={}
while q:
 p=q.popleft();m=p[-1]
 if m in seen:continue
 seen.add(m)
 if m in failed:paths[m]=p
 for n in g['modules'][m].get('imports',[]):q.append(p+[n])
longest={}
def cost(m):
 if m in longest:return longest[m][0]
 x=g['modules'][m]
 if x['kind']=='trusted-library' or state.get(m)=='passed':longest[m]=(0,None);return 0
 ns=x.get('imports',[]);n=max(ns,key=cost) if ns else None;longest[m]=(1+(cost(n) if n else 0),n);return longest[m][0]
cost('Rc7_Top');p=[];m='Rc7_Top'
while m:p.append(m);m=longest[m][1]
out={'selected_repository_modules':len(g['order']),'unresolved_source_selections':g['unresolved'],'state_counts':dict(collections.Counter(state[m] for m in g['order'])),'source_attempts_this_job':len(sources),'fresh_modules_passed_total':sum(state.get(m)=='passed' for m in g['order']),'ready_unattempted':ready,'failures':failed,'failure_paths_from_top':paths,'remaining_critical_path_lower_bound':longest['Rc7_Top'][0],'remaining_critical_path':p,'target_state':state.get('Rc7_Top'),'source_hash_errors':errors,'qualification':'Partial actual-source graph; unknown imports beyond unresolved sources may extend the closure. Critical path is a lower bound. No historical repository object substitutes for a blocked vertex.'}
(E/'RPz2_frontier.json').write_text(json.dumps(out,indent=2)+'\n');(E/'RPz2_receipt-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n');print(out['state_counts'],'ready',ready,'critical remaining',out['remaining_critical_path_lower_bound'],'hash errors',len(errors))
