"""Focused evidence and source-coherence checks; no semantic closure inferred."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[2]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/quotient231'
lean=json.loads((e/'lean-summary.json').read_text());native=json.loads((e/'native-summary.json').read_text())
assert lean['compiles']==59 and lean['remaining']==41
assert sum(x['exit_status']==0 for x in lean['attempts'])==45
assert [x['attempt'] for x in lean['attempts']]==list(range(23100,23159))
for x in lean['attempts']:
 r=json.loads((e/'lean'/f"{x['attempt']}-receipt.json").read_text())
 assert hashlib.sha256((e/'lean'/f"{x['attempt']}.lean.txt").read_bytes()).hexdigest()==r['source_sha256']
 assert r['limits']==dict(lean_memory_mb=7000,memory_high='6G',memory_max='8G',swap_max=0,tasks_max=128)
 assert '\n\tSwaps: 0\n' in r['time_log']
 if r['exit_status']==0:
  assert not r['errors']
  for s in r['print_axioms']:
   if 'depends on axioms: [' in s:
    assert set(z.strip() for z in s.split('depends on axioms: [')[1][:-1].replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
a=json.loads((e/'lean/23158-receipt.json').read_text());assert a['exit_status']==0 and len(a['print_axioms'])==50
b=json.loads((e/'final-object-binding.json').read_text());assert b['all_current_objects_match'] and b['all_current_sources_match'] and not b['compiled_dependency_mismatches']
assert len(b['dependency_objects'])==1252 and len(b['own_sources'])==45
for x in json.loads((e/'accepted-source-binding.json').read_text()):
 p=root/x['local_source'];s=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256']
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b',s)
 assert not re.search(r'\b(?:native_decide|maxHeartbeats|maxRecDepth)\b',s)
runs=[x for x in native['runs'] if 'kani' in x['target']]
assert len(runs)==15 and sum(x['exit_status']==0 for x in runs)==10 and sum(x['exit_status']==124 for x in runs)==4
for x in runs:
 assert x['swaps']==0
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
assert 'open64' in (e/'native/pdict-q231-kani-043/stdout.log').read_text()
assert "Can't copy a mutable borrow" in (e/'native/pdict-q231-array-translate-001/stdout.log').read_text()
assert json.loads((e/'initial-extraction-wrapper.json').read_text())
cpp=root/'tools/prover-dict-20261026/proof-quotient/lib.rs';s=cpp.read_text()
assert not re.search(r'kani::stub|no_mangle|no-unwinding-checks|no-default-checks',s)
entries=json.loads((e/'entries.json').read_text());assert entries['after']['selected']==175 and entries['after']['native_types']==26
changes=subprocess.check_output(['git','diff','--name-only','4cd294bc60'],cwd=root,text=True).splitlines()
assert not any(s.startswith(('crates/','programs/')) for s in changes)
assert not any('/R1Z/ProverRw' in s or '/R1Z/PV_CB_' in s or '/R1Z/PV_RunJoin_' in s for s in changes)
y=dict(result='pass',lean_compiles=59,lean_passed=45,lean_rejected=14,lean_remaining=41,kani_runs=15,kani_passed=10,kani_timeouts=4,kani_unsupported_boundary=1,audit_standard_only_reports=50,dependency_objects=1252,own_sources=45,source_selected_before=172,source_selected_after=175,source_open_after=80,native_types=26,root_premises_removed=0,target_established=False,qualification='Focused cached consistency only; native quotient/OS-world interpretation unresolved. Admission timing deviation is retained separately. No frozen release replay.')
(e/'validation-summary.json').write_text(json.dumps(y,indent=2)+'\n');print(json.dumps(y))
