"""Validate the BEi evidence packet without running a prover or a build."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('BEi_*/receipt.json'))]
assert len(receipts)==17
allowed={'propext','Classical.choice','Quot.sound'}
latest={};failed=[]
for d in receipts:
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
 assert int(d['swaps'])==0
 for name,h in d['source_hashes'].items():assert sha(E/d['attempt']/'sources'/name)==h
 if d['exit_status']:
  failed.append(d['attempt']);continue
 for line in d['print_axioms']:
  assert 'sorryAx' not in line
  m=re.search(r'axioms: \[([^]]*)\]',line)
  assert not m or set(m.group(1).split(', '))<=allowed,line
 for name in d['sources']:latest[name]=d
modules=sorted((R/'lean').glob('BEi_*.lean'))
assert len(modules)==12
for p in modules:
 d=latest[p.name]
 assert sha(p)==d['source_hashes'][p.name],p
 assert not re.search(r'(?m)^\s*(?:sorry|admit|axiom|native_decide)\b',p.read_text())
 assert not re.search(r'set_option\s+(?:maxHeartbeats|maxRecDepth)',p.read_text())
 names=re.findall(r'(?m)^theorem (\w+)',p.read_text())
 for name in names:
  assert '#print axioms '+name in p.read_text(),(p,name)
  assert any("."+name+"' " in line for line in d['print_axioms']),(p,name)
assert (E/'BEi_BEFORE_Top.lean.txt').read_bytes()==(E/'BEi_AFTER_Top.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
assert (E/'BEi_BEFORE_statement.lean.txt').read_bytes()==(E/'BEi_AFTER_statement.lean.txt').read_bytes()
count=json.loads((E/'BEi_recount.json').read_text())
assert count['before']==count['after'] and not count['removed'] and not count['added']
stop=json.loads((E/'BEi_018-stop.json').read_text())
assert not stop['compile_launched'] and not stop['source_uploaded']
assert not (E/'BEi_018'/'receipt.json').exists()
summary={'lean_compile_attempts':len(receipts),'lean_passed':sum(d['exit_status']==0 for d in receipts),'lean_failed':failed,'reservation_only_not_run':['BEi_018'],'kani_runs':0,'lean_budget':100,'kani_budget':20,'checked_new_modules':len(modules),'printed_successful_axiom_audits':sum(len(d['print_axioms']) for d in receipts if d['exit_status']==0),'wall_seconds':sum(d['wall_seconds'] for d in receipts),'maximum_peak_rss_kib':max(int(d['peak_rss_kib']) for d in receipts),'swaps':0,'actual_root_premise_delta':count['delta'],'root_unchanged':True,'blocking_error':stop['error'],'new_module_sources':{str(p.relative_to(R)):sha(p) for p in modules},'accepted_final_theorem_audits':{p.name:latest[p.name]['print_axioms'] for p in modules},'note':'Static packet check only; no new Lean/Kani/Rust/package or frozen-release replay.'}
(E/'BEi_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['new_module_sources','accepted_final_theorem_audits']},indent=2))
