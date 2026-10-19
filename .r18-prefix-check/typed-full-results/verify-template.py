#!/usr/bin/env python3
"""Verify exact sources, producing receipts, dependency hashes and axiom audits."""
from pathlib import Path
import hashlib,json,re,subprocess
b=Path(__file__).resolve().parent
root=b.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
base=b.parent/'r18-prefix-semantic-low-20261016'
prior=json.loads((base/'input-manifest-semantic-low-a.json').read_text())
prior_outputs=json.loads((base/'output-object-pins.json').read_text())
expected=dict(prior['new_import_objects'])
expected.update({n.replace('.','/')+'.olean':h for n,h in prior_outputs.items()})
pins={x['module']:x for x in json.loads((b/'source-pins.json').read_text())}
plan=json.loads((b/'attempt-plan.json').read_text())
produced={}; reports_total=0
for a in plan:
 d=b/'runs'/a['attempt'];r=json.loads((d/'receipt.json').read_text())
 mp=b/('input-manifest-'+a['attempt']+'.json');m=json.loads(mp.read_text())
 assert r['target']==a['module'] and r['exit_status']==a['exit_status']
 assert r['source_sha256']==sha(d/'source.lean') and r['runner_sha256']==sha(d/'runner.py')
 assert r['input_manifest_sha256']==sha(mp)
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
 assert '4.32.0' in r['lean_version'] and len(r['runtime_sha256'])==4
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['memory_events_before']==r['memory_events_after']
 assert m['current_semantic_cache']==prior['current_semantic_cache']
 for line in (d/'source.lean').read_text().splitlines():
  if not line.startswith('import '):continue
  for module in line[7:].split():
   key=module.replace('.','/')+'.olean'
   if key in expected:assert m['new_import_objects'][key]==expected[key],(a,module)
   elif module=='Mathlib.Tactic':
    assert json.loads((base/'full-inventory.json').read_text())['modules']['R1RetainedFieldByteCodec']['direct_import_objects'][module]=='55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8'
   else:raise AssertionError(('unattested direct import',a,module))
 if r['exit_status']:
  assert r['olean_sha256'] is None
  continue
 assert r['olean_sha256']
 source=(d/'source.lean').read_bytes()
 if a['module'] in pins:
  pin=pins[a['module']]
  assert source==subprocess.check_output(['git','show',pin['source_revision']+':'+pin['source']],cwd=root)
  assert r['source_sha256']==pin['source_sha256']
 else:assert source==(root/'docs/research/100bit-spend-path-20261013/lean'/(a['module']+'.lean')).read_bytes()
 log=(d/'lean.log').read_text()
 axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
 empty=re.findall(r"'([^']+)' does not depend on any axioms",log)
 assert len(axioms)+len(empty)==a['reports'],(a,len(axioms),len(empty))
 assert all({s.strip() for s in ax.split(',') if s.strip()}<=allowed for _,ax in axioms)
 assert 'sorryAx' not in log and 'error:' not in log
 reports_total+=a['reports'];produced[a['module']]=r['olean_sha256']
 expected[a['module'].replace('.','/')+'.olean']=r['olean_sha256']
assert produced==json.loads((b/'output-object-pins.json').read_text())
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print(f'PASS:{len(produced)} focused targets;{reports_total} standard-only reports; retained failed attempts; current coherent source/import/runtime/resource/output pins')
