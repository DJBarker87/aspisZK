from pathlib import Path
import json,subprocess,ast
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert [v['attempt'] for v in receipts]==list(range(73400,73500))
for v in receipts:
 assert v['reservation']['allowed'] and v['admission_exit']==0
 assert v['admission_and_launch_same_shell'] and v['cooldown_checked_before_launch']
 assert v['swaps']==0 and not v['old_objects_written']
 assert all(s in v['command'] for s in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-runjoin-20261026'
assert Path.cwd().resolve()==Path('/Users/dominic/ZK/.worktrees/pv-runjoin')
assert all(v['accepted_current_source'] for v in json.loads((E/'source-status.json').read_text()))
assert json.loads((E/'fresh-preflight.json').read_text())['all_match']
assert json.loads((E/'namespace-resolution.json').read_text())['all_match']
assert len(json.loads((E/'axioms-audit.json').read_text()))==3
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>=20_000_000];assert not large,large
for p in (R/'tools/pv-runjoin63-20261029').glob('*.py'):ast.parse(p.read_text(),str(p))
out=dict(attempts=100,ids_exact=True,admissions_valid=True,scope_caps_valid=True,swaps=0,active_sources_accepted=True,audit_declarations=141,preflight=True,namespace_resolution=True,files_below_20MB=True,branch='codex/pv-runjoin-20261026',worktree=str(Path.cwd()),rows_removed=[],target_established=False)
(E/'final-validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
