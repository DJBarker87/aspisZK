#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
b=Path(__file__).resolve().parent;root=b.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=b/'cache';inventory=json.loads((cache/'framing-reuse-audit.json').read_text())['modules'];pins={e['module']:e for e in json.loads((cache/'current-source-pins.json').read_text())}
assert len(inventory)==len(pins)==17
for module,e in inventory.items():
 p=cache/'receipts'/(module+'.json');r=json.loads(p.read_text())
 assert sha(p)==e['receipt_sha256'] and r['exit_status']==0
 assert sha(cache/'sources'/(module.replace('.','/')+'.lean'))==e['source_sha256']==r['source_sha256']==pins[module]['source_sha256']
 assert r['output_sha256']==e['object_sha256']
 assert r['direct_imports']==e['direct_import_pins']
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axiom_reports'])
 committed=subprocess.check_output(['git','show',pins[module]['source_revision']+':'+pins[module]['source']],cwd=root)
 assert hashlib.sha256(committed).hexdigest()==e['source_sha256']
 for dep in r['direct_imports']:
  if dep['module'] in inventory:assert dep['object_sha256']==inventory[dep['module']]['object_sha256']
  else:assert dep['module'].startswith(('Mathlib.','Lean.'))
targets={e['module']:e for e in json.loads((b/'target-source-pins.json').read_text())}
attempts={'framing-lemma-a':('FS2.LemmaA',0,2),'framing-theorem-a':('FS2.Theorem',0,3),'framing-duplex-a':('FS2.Duplex',1,0)}
for a,(module,code,count) in attempts.items():
 d=b/'runs'/a;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==code
 assert r['source_sha256']==sha(d/'source.lean')==targets[module]['source_sha256']
 assert r['runner_sha256']==sha(d/'runner.py')
 assert r['input_manifest_sha256']==sha(b/('input-manifest-'+a+'.json'))
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['memory_events_before']==r['memory_events_after']
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
 assert r['runtime_sha256'] and '4.32.0' in r['lean_version']
 log=(d/'lean.log').read_text()
 if code==0:
  reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);assert len(reports)==count
  for _,ax in reports:assert set(x.strip() for x in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'}
  assert 'sorryAx' not in log and 'error:' not in log
 else:
  assert r['olean_sha256'] is None and 'sorryAx' in log
  assert 'maximum recursion depth' in log and 'failed to prove positivity' in log
for line in (b/'SHA256SUMS').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(b/p)==h,p
print('PASS:17 attested current-source cache inputs; two green targets/five standard-only audits; rejected Duplex failure retained, no accepted failed output')
