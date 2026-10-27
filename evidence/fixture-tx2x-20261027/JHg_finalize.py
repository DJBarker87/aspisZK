"""Compile-free receipt/source audit after the strict100-process stop."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];accepted={}
for p in sorted(P.glob('JHg_TX2_???/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
 if r['exit_status']==0:
  for f,h in r['source_hashes'].items():
   src=R/'lean'/f
   if src.exists() and sha(src)==h:accepted[src.stem]=dict(module=src.stem,source_sha256=h,receipt=str(p.relative_to(R)),attempt=r['attempt'],axioms=r['print_axioms'])
assert len(receipts)==100,len(receipts)
current={p.stem for p in (R/'lean').glob('JHg_*.lean')}
assert current==set(accepted),(sorted(current-set(accepted)),sorted(set(accepted)-current))
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 a=json.loads((P/(r['attempt']+'-reservation.json')).read_text());assert a['allowed'] is True
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    names=set(re.search(r'\[([^\]]*)\]',line)[1].split(', '))
    assert names <= {'propext','Classical.choice','Quot.sound'},line
allsource='\n'.join(p.read_text() for p in (R/'lean').glob('JHg_*.lean'))
forbidden=re.findall(r'^\s*(?:axiom\b|.*\b(?:sorry|admit|native_decide)\b|set_option max(?:Heartbeats|RecDepth)\b).*$',allsource,re.M)
assert not forbidden,forbidden
missing_print=[]
for p in (R/'lean').glob('JHg_*.lean'):
 s=p.read_text()
 for name in re.findall(r'^theorem (\w+)',s,re.M):
  if not re.search(r'^#print axioms '+re.escape(name)+r'\b',s,re.M):missing_print.append((p.name,name))
assert not missing_print,missing_print
(P/'JHg_VALIDATION.json').write_text(json.dumps(accepted,indent=2)+'\n')
rows=[]
for r in receipts:
 rows.append({k:r[k] for k in ['attempt','sources','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
(P/'JHg_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
retry=[dict(attempt=p.stem,retries=json.loads(p.read_text())) for p in sorted(P.glob('*-retries.json')) if json.loads(p.read_text())]
summary=dict(lean_processes=len(receipts),lean_budget=100,passing=sum(r['exit_status']==0 for r in receipts),rejecting=sum(r['exit_status']!=0 for r in receipts),current_checked_sources=len(accepted),kani_runs=0,kani_budget=10,total_lean_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_swaps=sum(int(r['swaps']) for r in receipts),pressure_failures=[r['attempt'] for r in receipts if r['exit_status'] in [124,134,137]],reservation_retries=retry,budget_status='STOPPED: no101st process',admission='Controller checks exit0 AND allowed:true before upload; final reservation receipts all allowed:true',target='not yet established',premises_removed=0)
(P/'JHg_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
static=dict(forbidden_source_tokens=forbidden,missing_axioms_prints=missing_print,all_current_sources_have_exact_passing_receipts=True,shipped_changes=False,binary_artifacts_committed=False,source_count=len(current))
(P/'JHg_STATIC.json').write_text(json.dumps(static,indent=2)+'\n')
print(json.dumps(summary,indent=2))
