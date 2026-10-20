#!/usr/bin/env python3
"""Validate selected candidate-2 source-factorization and focused receipts."""
from pathlib import Path
import hashlib,json,subprocess,sys
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-profiling-marker.py','check-profiling-source.py']:subprocess.run([sys.executable,str(here/script),'--check'],check=True)
r=json.loads((ev/'PROFILING-CANDIDATE2-FINAL.json').read_text())
assert r['candidate']=='190e1779c3b9530047e4d2dfcdf0022b200d6c35'
assert r['parent']=='0330ae7300b3df6602600a727dfd1b969bfbe19a'
assert not r['direct_whole_program_emission'] and not r['additional_interpreter'] and not r['candidate_equivalence_assumption']
assert r['source_audit_sha256']==sha((here/'profiling-source-audit/source-audit.json').read_bytes())
objects={x['module']:x['object_sha256'] for x in r['selected']}
for entry in r['selected']:
 receipt=ev/entry['attempt']/'receipt.json';assert entry['receipt_sha256']==sha(receipt.read_bytes())
 rec=json.loads(receipt.read_text());source=(area/'lean'/(entry['module']+'.lean')).read_bytes()
 assert rec['exit_status']==0 and rec['source_sha256']==sha(source)==entry['source_sha256']
 checked=source+''.join('\n#print axioms '+decl+'\n' for decl in rec['audit_declarations']).encode();assert sha(checked)==rec['checked_source_sha256']
 assert rec['print_axioms_output']==entry['print_axioms'] and rec['print_axioms_output'].strip()
 for forbidden in ['sorryAx','native_decide','Lean.ofReduceBool','Lean.trustCompiler']:assert forbidden not in rec['print_axioms_output'],forbidden
 assert entry['swap']==0
 for imp in rec['direct_imports']:
  # Parent report records exact shared cache provenance as well as dependencies.
  name=imp.get('module')
  if name in objects:assert imp.get('object_sha256',imp.get('sha256'))==objects[name],imp
for name,expected in r['raw_emission'].items():
 raw=(here/'profiling-marker-generated'/name).read_bytes();assert sha(raw)==expected and raw==(area/'lean/AspisR1Profiling'/name).read_bytes()
# No production-source changes are part of this formal-only work package.
paths=['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/r1_semantic.rs','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']
for path in paths:assert (repo/path).read_bytes()==subprocess.check_output(['git','-C',str(repo),'show',r['production_revision']+':'+path])
print(json.dumps(dict(candidate=r['candidate'],selected_targets=len(r['selected']),status=r['status'],savings=r['savings'],direct_whole_program_emission=False)))
