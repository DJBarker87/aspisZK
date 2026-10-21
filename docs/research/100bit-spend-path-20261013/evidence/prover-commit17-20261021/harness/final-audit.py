#!/usr/bin/env python3
"""Check exact evidence/source consistency, without rerunning any proof job."""
import json,hashlib,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda b:hashlib.sha256(b).hexdigest()
rows={}
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 for line in p.read_text().splitlines():
  r=json.loads(line);assert r['attempt'] not in rows;rows[r['attempt']]=r
assert sorted(rows)==list(range(8641,8656))
failed={8641,8643,8645,8646,8647,8651,8652,8653}
last={}
for a,r in sorted(rows.items()):
 assert r['source_sha256']==sha((E/'lean/sources'/f"attempt-{a}-{Path(r['module']).stem}.lean.txt").read_bytes())
 assert r['swaps']==0
 assert r['cgroup_memory_max_gib']==8 and r['memory_limit_mib']==7000
 assert r['accepted']==(a not in failed)
 out=(E/'lean'/f'out-{a}.log').read_text()
 assert 'env=J' in out and 'slot=/tmp/aspis-r0-lean-slot-' in out
 if r['accepted']:
  assert not r['errors']
  for line in r['axioms']:
   if 'depends on axioms:' in line:
    names=set(re.search(r'\[([^\]]*)\]',line,re.S)[1].replace('\n','').replace(' ','').split(','))
    assert names<= {'propext','Classical.choice','Quot.sound'},names
  last[r['module']]=r
for module,r in last.items():assert sha((L/module).read_bytes())==r['source_sha256'],module
assert len(rows[8655]['axioms'])==12
rust=json.loads((E/'rust-attempts.json').read_text());assert len(rust)==10
for r in rust:
 assert r['accepted'] and r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 assert 'VERIFICATION:- SUCCESSFUL' in (E/'receipts'/r['name']/'stdout.log').read_text()
 if 'push' in r['name'] or r['name'].startswith('padding-row'):
  suffix='iteration17v2.rs' if r['name'].endswith('v2') else 'iteration17.rs'
  actual=(E/'rust-sources/state-only-before17.rs').read_bytes()+(E/'rust-sources'/suffix).read_bytes()
  assert sha(actual)==r['source_hashes']['crates/aspis-prover/src/state_only_hiding.rs']
for name in ['assembly-charon-v1','assembly-aeneas-v1']:
 r=json.loads((E/'receipts'/name/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0
 pins=json.loads((E/(name+'-inputs.json')).read_text())
 assert pins['source_hashes']['crates/aspis-prover/src/prover_commit_reference.rs']==sha((E/'extraction/reference-with-assembly.rs').read_bytes())
for p in json.loads((E/'extraction/promotion.json').read_text()):
 assert p['promoted_sha256']==sha((L/Path(p['module'].replace('.','/')).with_suffix('.lean')).read_bytes())
assert not json.loads((E/'extraction/llbc.json').read_text())['has_errors']
assert (E/'endpoint-before.lean.txt').read_bytes()==(E/'endpoint-after.lean.txt').read_bytes()==(L/'R1Z/PrivacyR1HeadlineDeployed.lean').read_bytes()
subprocess.run(['python3',str(E/'harness/check-source.py'),'--check'],check=True)
# This work adds proof-only code and evidence, without production edits.
changed=subprocess.check_output(['git','diff','--name-only','47ccfa22c','--','crates'],text=True)
assert not changed
result=dict(status='PASS',lean_attempts=15,accepted_lean_attempts=sorted(set(rows)-failed),excluded_lean_attempts=sorted(failed),kani_successes=10,extraction_successes=2,final_axiom_reports=12,endpoint_changed=False,whole_run_instances_constructed=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),claim='Focused local component evidence only; shipped-prover target not yet established.')
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
