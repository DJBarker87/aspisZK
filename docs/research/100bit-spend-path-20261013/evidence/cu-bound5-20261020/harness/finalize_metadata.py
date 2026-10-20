"""Refresh current-definition citations and verify no numerical/classification change."""
import json,subprocess,sys
from pathlib import Path
H=Path(sys.argv[1]);A=H/'analysis';read=lambda p:json.loads(p.read_text())
b=read(A/'bound.json');numeric={k:b[k] for k in ['B','per_kind','sweep','verdict']}
r0=read(H/'harness/rules.json')
subprocess.run([sys.executable,str(H/'harness/candidate_rules.py'),str(H),str(A),str(H/'harness/rules-rebased.json'),str(H/'harness/rules.json')],check=True)
r=read(H/'harness/rules.json')
# Only citations change: compare every operational exclusion/cap selector/value.
strip=lambda x:[{k:v for k,v in e.items() if k not in ['citation','citation_revision','predecessor_citation']} for e in x]
assert all(strip(r[c])==strip(r0[c]) for c in ['loop_caps','exclusions','callee_caps'])
subprocess.run([sys.executable,str(H/'harness/make_deliverables.py'),str(A),str(H/'harness/rules.json'),str(H/'variants-measured.json'),str(A)],check=True)
subprocess.run([sys.executable,str(H/'harness/new_path_audit.py'),str(H)],check=True)
assert numeric=={k:read(A/'bound.json')[k] for k in numeric}
(H/'definition-audit.json').write_text(json.dumps(dict(source_revision='c16e59e77',operational_rules_unchanged=True,bounds_unchanged=True,current_source_caps={e['id']:e['citation'] for c in ['loop_caps','exclusions'] for e in r[c] if e.get('citation_revision','').startswith('c16e59e77')},method='Read current Rust definitions and bound ELF counters; not a Lean proof'),indent=1)+'\n')
subprocess.run([sys.executable,str(H/'harness/package_check.py'),str(H)],check=True)
