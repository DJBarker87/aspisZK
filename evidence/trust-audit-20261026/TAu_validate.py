"""Validate retained receipts and accounting without invoking Lean."""
from pathlib import Path
import hashlib,json,re,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for i in range(1,31):
 a=f'TAu_{i:03d}';p=E/a/'receipt.json';r=json.loads(p.read_text());receipts.append(r)
 assert r['attempt']==a and r['command'][3:6]==['-j1','-M7000','-DElab.async=false']
 assert len(r['sources'])==1 and '-o' not in r['command']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0' and r['exit_status'] in [0,1]
 for src,h in r['source_hashes'].items():
  assert sha(E/a/'sources'/src)==h
  assert (E/src).read_bytes()==(E/a/'sources'/src).read_bytes()
  for line in (E/src).read_text().splitlines():
   assert not line.strip() or line.startswith(('import ','#print ','#check ','--')),line
 assert json.loads((E/(a+'-reservation.json')).read_text())['allowed']
 assert not list(E.glob(a+'-barrier-[1-9]*.log'))
assert sum(r['exit_status']==0 for r in receipts)==13
for target in ['FGl_Headline','Rc6_Top']:
 assert (E/f'TAu_{target}_BEFORE.lean.txt').read_bytes()==(E/f'TAu_{target}_AFTER.lean.txt').read_bytes()
results=json.loads((E/'TAu_kernel-results.json').read_text())
for n in ['AspisR1.FGl_Headline.deployed','AspisR1.Rc6_Top.deployed','AspisR1.FGl_Nonvacuity.composed']:
 assert {'attempt':'TAu_001','axioms':['propext','Classical.choice','Quot.sound']} in results['declarations'][n]
 assert all(r['axioms']==['propext','Classical.choice','Quot.sound'] for r in results['declarations'][n])
assert len(results['nonstandard_axioms'])==67
assert results['declarations']['Aeneas.Std.core.fmt.Formatter']==[dict(attempt='TAu_004',axioms=[])]
assert 'Aeneas.Std.core.fmt.Formatter' in results['declarations']['Aeneas.Std.core.error.Error.mk.inj'][0]['axioms']
coverage=json.loads((E/'TAu_module-coverage.json').read_text())
assert len(coverage['modules'])==10389 and coverage['printed_modules']==9488
closure=json.loads((E/'TAu_closure.json').read_text())
for p in closure['parts']:assert sha(E/p['path'])==p['sha256']
assert len(closure['missing'])==4
subprocess.run(['python3',str(E/'TAu_recount.py')],check=True)
out=dict(lean_attempts=30,kani_runs=0,passing_invocations=13,diagnostic_failed_invocations=17,
 command_wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,
 standard_only_headline_results=True,nonstandard_imported_dependency_names=67,exhaustive_closure_audit_complete=False,
 mathematical_premises_removed=0,proposed_P_to_G_reclassifications=13,L188='OPEN',
 note='No new proof or release replay. Failures/gaps and stored Formatter-summary discrepancy remain findings.')
(E/'TAu_validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
