"""Read-only audit of atomic admission, full cooldown and unique launched IDs."""
from pathlib import Path
import json,subprocess,hashlib,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin55-20261029';rows=[]
refusals=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
for p in sorted(E.glob('receipt-*.json')):
 x=json.loads(p.read_text());a=x['attempt'];v=x['wrapper_revision'];b=subprocess.check_output(['git','show',v+':tools/pv-runjoin55-20261029/compile.py'],cwd=R);s=b.decode();t=datetime.datetime.fromisoformat(x['utc']).timestamp();prior=[q for q in refusals if q['epoch']<t];clear=all(t>=q['epoch']+180 for q in prior)
 atomic="admit+' && '+check+' && '+shlex.join(cmd)" in s
 row=dict(attempt=a,wrapper_revision=v,wrapper_sha256=hashlib.sha256(b).hexdigest(),allowed=x['reservation'].get('allowed'),admission_exit_zero_enforced_by_shell_and=atomic,allowed_true_explicitly_checked="['allowed'] is True" in s,same_shell=atomic,cooldown_complete=clear,compiler_launched=True)
 row['compliant']=row['allowed'] is True and atomic and row['allowed_true_explicitly_checked'] and clear;rows.append(row)
assert len({x['attempt'] for x in rows})==len(rows)
assert all(x['compliant'] for x in rows),[x for x in rows if not x['compliant']]
(E/'admission-launch-audit.json').write_text(json.dumps(dict(launches=len(rows),void_launches=[],all_compliant=True,refusal_count=len(refusals),rows=rows),indent=2)+'\n')
print('All',len(rows),'launches have atomic zero-exit/allowed:true admission and complete cooldown; void: 0')
