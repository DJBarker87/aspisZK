from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];accepted={};records=[]
for f in sorted(P.glob('JFo_[0-9][0-9][0-9]/receipt.json')):
 v=json.loads(f.read_text());v['receipt']=str(f.relative_to(R));receipts.append(v)
 rows=[]
 for name,h in v['source_hashes'].items():
  rows.append(dict(module=name,sha256=h,snapshot=str((f.parent/'sources'/name).relative_to(R))))
  assert sha(f.parent/'sources'/name)==h
  if v['exit_status']==0:
   assert all('sorryAx' not in a for a in v.get('print_axioms',[]))
   for a in v.get('print_axioms',[]):
    if '[' in a:assert set(a.rsplit('[',1)[1].rstrip(']').split(', '))<={'propext','Classical.choice','Quot.sound'},a
   accepted[(name,h)]=v
 records.append(dict(attempt=v['attempt'],exit_status=v['exit_status'],wall_seconds=v['wall_seconds'],peak_rss_kib=v['peak_rss_kib'],swaps=v['swaps'],source_revision=v['source_revision'],sources=rows,print_axioms=v.get('print_axioms',[]),receipt=v['receipt'],limits=v['limits'],deps_fingerprint=v['deps_fingerprint']))
final=[];pending=[]
for f in sorted((R/'lean').glob('JFo_*.lean')):
 v=accepted.get((f.name,sha(f)))
 if not v:pending.append(f.name);continue
 s=f.read_text();ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 for t in re.findall(r'^theorem (\w+)',s,re.M):
  assert '#print axioms '+t in s,(f,t)
  assert any(ns+'.'+t in a for a in v.get('print_axioms',[])),(f,t)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|maxHeartbeats|maxRecDepth',s,re.M),f
 final.append(dict(module=f.name,source_sha256=sha(f),receipt=v['receipt'],axioms=v.get('print_axioms',[])))
summary=dict(charged_requests=len(list(P.glob('JFo_[0-9][0-9][0-9].json'))),lean_processes=len(receipts),passed=sum(v['exit_status']==0 for v in receipts),rejected=sum(v['exit_status']!=0 for v in receipts),pre_lean_inventory_failures=1,kani_runs=0,checked_current_modules=len(final),pending=pending,total_lean_wall_seconds=sum(v['wall_seconds'] for v in receipts),peak_rss_kib=max(int(v['peak_rss_kib']) for v in receipts),swaps=sum(int(v['swaps']) for v in receipts),actual_top_premise_delta=0,full_joint_nonvacuity=False,accepted2_delivered=False)
(P/'JFo_VALIDATION.json').write_text(json.dumps(final,indent=2)+'\n')
(P/'JFo_RECORDS_MANIFEST.json').write_text(json.dumps(records,indent=2)+'\n')
(P/'JFo_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
