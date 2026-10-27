"""Offline validation of SCK sources, receipts, scope and zero-delta recount."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=sorted(E.glob('SCK_[0-9][0-9][0-9]/receipt.json'))
receipts=[json.loads(p.read_text()) for p in paths]
assert len(receipts)<=30
assert [r['attempt'] for r in receipts]==[f'SCK_{n:03}' for n in range(1,len(receipts)+1)]
excluded=json.loads((E/'SCK_EXCLUDED_ATTEMPTS.json').read_text())
axioms=[]
for path,r in zip(paths,receipts):
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},path
 assert int(r['swaps'])==0 and '-M7000' in r['command'] and '-j1' in r['command'],path
 assert r['source_revision'] and r['deps_fingerprint']['selected_objects'],path
 for name,digest in r['source_hashes'].items():
  assert name.startswith('SCK_') and sha(path.parent/'sources'/name)==digest,(path,name)
 if r['exit_status']==0 and r['attempt'] not in excluded:
  assert r['print_axioms'] or r['attempt']=='SCK_001',path
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    values=set(re.split(r'\s*,\s*',line.split('depends on axioms:',1)[1].strip().strip('[]')))
    assert values<={'propext','Classical.choice','Quot.sound'},(path,line)
  axioms+=r['print_axioms']
for source in sorted((R/'lean').glob('SCK_*.lean')):
 text=source.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|set_option\s+(maxHeartbeats|maxRecDepth)|^\s*axiom\s',text,re.M),source
 if '--final' in sys.argv:
  assert any(r['exit_status']==0 and r['attempt'] not in excluded and r['source_hashes'].get(source.name)==sha(source) for r in receipts),source
  namespace=re.search(r'^namespace\s+(\S+)',text,re.M)
  for name in re.findall(r'^theorem\s+(\w+)',text,re.M):
   assert namespace and any("'"+namespace[1]+'.'+name+"'" in line for line in axioms),(source,name)
ledger=json.loads((E/'SCK_LEDGER_DELTA.json').read_text())
rows=ledger['rows']
for mode in ['raw','distinct']:
 selected=rows if mode=='raw' else [r for r in rows if r['id'] not in ['L137','F3Y_G_L137']]
 for scope,counts in ledger['before'][mode].items():
  selected_scope=[r for r in selected if r['scope']!='deployment alias'] if scope=='deduplicated actual plus non-alias deployment' else [r for r in selected if r['scope']==scope]
  actual={c:sum(r['classification']==c for r in selected_scope) for c in ['T','P','G','C']}
  assert counts==actual,(mode,scope)
assert ledger['before']==ledger['after']
assert not ledger['removed_rows'] and not ledger['added_rows'] and not ledger['reclassified_rows']
assert (E/'SCK_BEFORE_SOURCE.lean.txt').read_bytes()==(E/'SCK_AFTER_SOURCE.lean.txt').read_bytes()==(R/'lean/Rc8_Top.lean').read_bytes()
base=receipts[0]['source_revision']
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith(('lean/SCK_','evidence/l159-scope-20261026/','design/L159-DECISION-20261026.md')) for p in changed+untracked),(changed,untracked)
if '--final' in sys.argv:
 assert len(receipts)==30
 assert set(excluded)=={'SCK_002','SCK_004','SCK_005'}
 assert all(r['exit_status']==0 or r['attempt'] in excluded for r in receipts)
 assert (E/'SCK_BEFORE_KERNEL.lean.txt').read_bytes()==(E/'SCK_AFTER_KERNEL.lean.txt').read_bytes()
 plan=json.loads((E/'SCK_INVENTORY_PLAN.json').read_text())
 for task in plan:
  r=receipts[task['attempt']-1]
  assert r['sources']==[task['module']+'.lean'] and r['exit_status']==0
  assert r['source_hashes'][r['sources'][0]]==sha(R/'lean'/r['sources'][0])
  log=(E/r['attempt']/'stdout.log').read_text()
  assert all(c in log for c in task['constants'])
summary=dict(Lean_attempts=len(receipts),Kani_runs=0,passed=sum(r['exit_status']==0 and r['attempt'] not in excluded for r in receipts),development_failures=sum(r['exit_status']!=0 or r['attempt'] in excluded for r in receipts),compiler_exit_failures=sum(r['exit_status']!=0 for r in receipts),excluded_exit_zero_axiom_diagnostics=sum(r['exit_status']==0 and r['attempt'] in excluded for r in receipts),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,root='AspisR1.Rc8_Top.deployed',removed_actual_premises=0,raw_counts=ledger['after']['raw'],distinct_counts=ledger['after']['distinct'],source_only_scope=True,axioms='accepted attempts: subsets of propext, Classical.choice, Quot.sound; three excluded development attempts retained',budget_exhausted=len(receipts)==30)
(E/'SCK_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in receipts))
(E/'SCK_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
