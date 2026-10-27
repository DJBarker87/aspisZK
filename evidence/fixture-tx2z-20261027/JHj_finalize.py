from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];accepted={}
for p in sorted(P.glob('JHj_TX2_???/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert json.loads((P/(r['attempt']+'-reservation.json')).read_text())['allowed'] is True
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    names=set(re.search(r'\[([^\]]*)\]',line)[1].split(', '));assert names<={'propext','Classical.choice','Quot.sound'},line
  for f,h in r['source_hashes'].items():
   src=R/'lean'/f
   if src.exists() and sha(src)==h:accepted[src.stem]=dict(module=src.stem,sha256=h,receipt=str(p.relative_to(R)),attempt=r['attempt'],axioms=r['print_axioms'])
assert len(receipts)==100,len(receipts)
assert [r['attempt'] for r in receipts]==[f'JHj_TX2_{i:03}' for i in range(1,101)]
current={p.stem for p in (R/'lean').glob('JHj_*.lean')};assert current==set(accepted),(current-set(accepted),set(accepted)-current)
missing=[];forbidden=[]
for p in (R/'lean').glob('JHj_*.lean'):
 s=p.read_text()
 forbidden.extend((p.name,x) for x in re.findall(r'^\s*(?:axiom\b|.*\b(?:sorry|admit|native_decide)\b|set_option max(?:Heartbeats|RecDepth)\b).*$',s,re.M))
 for name in re.findall(r'^(?:@\[[^\n]*\] )?(?:private )?theorem (\w+)',s,re.M):
  if not re.search(r'^#print axioms '+re.escape(name)+r'\b',s,re.M):missing.append((p.name,name))
assert not forbidden,forbidden
assert not missing,missing
root=R/'evidence/replay-deployed2-20261027/RPx_Deployed.lean'
assert root.read_bytes()==(P/'JHj_BEFORE_RPx_Deployed.lean.txt').read_bytes()==(P/'JHj_AFTER_RPx_Deployed.lean.txt').read_bytes()
paths=subprocess.check_output(['git','diff','--name-only','4ed75a1a1c^'],cwd=R,text=True).splitlines()
assert all(x.startswith(('lean/JHj_','evidence/fixture-tx2z-20261027/')) for x in paths),paths
(P/'JHj_VALIDATION.json').write_text(json.dumps(accepted,indent=2)+'\n')
keys=['attempt','sources','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']
(P/'JHj_ATTEMPTS.jsonl').write_text(''.join(json.dumps({k:r[k] for k in keys})+'\n' for r in receipts))
retries=[dict(attempt=p.stem,retries=json.loads(p.read_text())) for p in sorted(P.glob('*-retries.json')) if json.loads(p.read_text())]
summary=dict(lean_processes=len(receipts),lean_budget=100,passing=sum(r['exit_status']==0 for r in receipts),rejecting=sum(r['exit_status']!=0 for r in receipts),current_checked_sources=len(accepted),kani_runs=0,kani_budget=10,total_lean_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_swaps=sum(int(r['swaps']) for r in receipts),pressure_failures=[r['attempt'] for r in receipts if r['exit_status'] in [124,134,137]],reservation_retries=retries,budget_status='STOP:100/100; no101st Lean process',admission='Controller requires exit0 AND allowed:true before upload; all recorded admission receipts allowed:true',target='not yet established',actual_headline_premises_removed=0)
(P/'JHj_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'JHj_STATIC.json').write_text(json.dumps(dict(forbidden_tokens=forbidden,missing_axioms_prints=missing,all_current_sources_have_exact_passing_receipts=True,source_count=len(current),changed_path_scope_checked=True,shipped_source_changes=False,headline_source_sha256=sha(root)),indent=2)+'\n')
# Assert that the canonical inherited JHi_ proofs are imported, without loading
# their retired audit wrappers or combining oversized environments.
hi={p.stem:p for p in (R/'lean').glob('JHi_*.lean')};seen=set()
def visit(n):
 if n in seen or n not in hi:return
 seen.add(n)
 for child in re.findall(r'^import (\w+)',hi[n].read_text(),re.M):visit(child)
for p in (R/'lean').glob('JHj_*.lean'):
 for child in re.findall(r'^import (\w+)',p.read_text(),re.M):visit(child)
canonical={n for n in hi if not n.startswith('JHi_Audit') and n!='JHi_TopAudit'}
assert canonical<=seen,canonical-seen
(P/'JHj_INHERITED_COVERAGE.json').write_text(json.dumps(dict(canonical_modules=sorted(canonical),reached=sorted(seen),all_canonical_inherited_modules_imported=True,retired_audit_wrappers_reused_as_evidence_only=True,headline_audited_separately=True),indent=2)+'\n')
print(json.dumps(summary,indent=2))
