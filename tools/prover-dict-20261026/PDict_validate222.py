"""Mechanical evidence checks only; no semantic/native closure inferred."""
from pathlib import Path
import json,re,hashlib,subprocess
root=Path(__file__).resolve().parents[2];e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/lift222'
s=json.loads((e/'lean-summary.json').read_text());assert s['compiles']==100 and s['remaining']==0
rows=s['attempts'];assert sorted(z['attempt'] for z in rows)==list(range(22200,22300))
assert sum(z['exit_status']==0 for z in rows)==53
seen=set()
for z in rows:
 x=json.loads((e/f"{z['attempt']}-receipt.json").read_text())
 assert x['module'].startswith('R1Z/PDict_')
 assert hashlib.sha256((e/f"{z['attempt']}.lean.txt").read_bytes()).hexdigest()==x['source_sha256']
 key=(x['source_sha256'],x['deps_fingerprint']);assert key not in seen;seen.add(key)
 assert x['limits']==dict(lean_memory_mb=7000,memory_high='6G',memory_max='8G',swap_max=0,tasks_max=128)
 assert '\n\tSwaps: 0\n' in x['time_log']
 if x['exit_status']==0:
  assert not x['errors']
  for report in x['print_axioms']:
   if 'depends on axioms: [' in report:
    assert set(z.strip() for z in report.split('depends on axioms: [')[1][:-1].replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
a=json.loads((e/'22299-receipt.json').read_text());assert len(a['print_axioms'])==433
reports={re.match(r"'([^']+)'",z)[1] for z in a['print_axioms']}
assert set(json.loads((e/'accepted-theorems.json').read_text()))<=reports
b=json.loads((e/'final-object-binding.json').read_text());assert b['all_objects_match'] and b['all_owned_sources_match']
assert len(b['dependency_objects'])==1246 and len(b['owned_sources'])==53
entries=json.loads((e/'entries.json').read_text());assert len(entries['functions'])==262 and len(entries['type_entries'])==28
ledger=subprocess.check_output(['git','show',entries['research_revision']+':design/PRIVACY-LEDGER-20261026.md'],text=True)
assert hashlib.sha256(ledger.encode()).hexdigest()==entries['ledger_sha256']
for x in json.loads((e/'accepted-source-binding.json').read_text()):
 p=root/x['local_source'];assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b',p.read_text())
 assert not re.search(r'\b(?:native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text())
changed=subprocess.check_output(['git','diff','--name-only','ea4fd01ba3'],text=True).splitlines()
assert not any(x.startswith(('crates/','programs/')) for x in changed)
assert not any('/R1Z/ProverRw' in x or '/R1Z/PV_RunJoin_' in x for x in changed)
assert not any(x in {'design/PRIVACY-LEDGER-20261026.md','design/PREMISE-LEDGER-20261025.md'} for x in changed)
y=dict(result='pass',lean_compiles=100,pass_count=53,rejected_count=47,kani_runs=0,kani_remaining=15,audit_reports=433,audit_standard_only=True,dependency_object_hashes=1246,own_source_hashes=53,source_fields=262,lower_types=28,source_counts_unchanged='172 selected /83 open /255 sufficient',exact_invocation_denominator=None,root_premises_removed=0,target_established=False,qualification='Mechanical evidence consistency only; stage1 incomplete, stages2/3 not begun; no frozen replay/native quotient.')
(e/'validation-summary.json').write_text(json.dumps(y,indent=2)+'\n');print(json.dumps(y))
