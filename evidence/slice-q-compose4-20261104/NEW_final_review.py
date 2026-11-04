"""Metadata-only closeout. No compiler, prover, extraction or release replay."""
from pathlib import Path
import json,hashlib,subprocess,datetime
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tests=(E/'NEW_FINAL_TESTS.stderr').read_text()
assert 'Ran 20 tests in 'in tests and tests.rstrip().endswith('OK'),tests
validation=json.loads((E/'NEW_FINAL_VALIDATION.stdout').read_text())
assert not(E/'NEW_FINAL_VALIDATION.stderr').read_text()
assert validation['q_functions_closed']==63 and validation['edge_closed']==187
assert set(validation['roots'].values())=={'OPEN'}
budget=json.loads((E/'NEW_BUDGET.json').read_text())
assert budget['executed']==dict(extract=4,kani=110,lean=80,native=4)
assert not(E/'NEW_FINAL_CHECKS.stderr').read_text()
cache=json.loads((E/'NEW_FINAL_CACHE.json').read_text());assert cache['cache_never_deleted']
proof=json.loads((E/'NEW_PROOF_AUDIT.json').read_text());assert proof['standard_axioms_only']
assert len(cache['exports'])==28
paths=[]
for p in sorted(E.rglob('*')):
 if not p.is_file()or '__pycache__'in p.parts or p.name in {'NEW_FINAL_REVIEW.json','NEW_ACTIVE.json'}:continue
 assert p.stat().st_size<=20*1024*1024,str(p)
 paths.append(dict(path=str(p.relative_to(E)),bytes=p.stat().st_size,sha256=sha(p)))
result=dict(status='EVIDENCE_RECORDED_ROOTS_OPEN',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_revision_before_final_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,validation=validation,validator_exit_status=0,tests=tests.strip(),tests_exit_status=0,metadata_audit=json.loads((E/'NEW_FINAL_CHECKS.stdout').read_text()),cache_exports=len(cache['exports']),formal_budget=budget,security_target_established=False,shipped_files_changed=False,keys_touched=False,pushed=False,files=paths)
(E/'NEW_FINAL_REVIEW.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(status=result['status'],evidence_files=len(paths),tests=20,formal_runs=198,cache_exports=28)))
