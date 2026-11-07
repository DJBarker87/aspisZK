"""Own sequential final gate; child merge is checked read-only before use."""
from pathlib import Path
import json,subprocess,sys,time
E=Path(__file__).resolve().parent
while len(list(E.glob('NMP_K[0-9][0-9][0-9]/receipt.json')))<100:time.sleep(5)
while(E/'NMP_CLIENT_ACTIVE').exists():time.sleep(1)
q=subprocess.run(['git','show','research:evidence/tx1-finish4-20261110/NMO_CLOSED.json'],capture_output=True,text=True)
r=dict(research_revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip(),present=q.returncode==0,method='git show only; no sibling worktree access',path='evidence/tx1-finish4-20261110/NMO_CLOSED.json')
if q.returncode==0:r['candidate']=json.loads(q.stdout)
(E/'NMP_CHILD136_GATE_CHECK.json').write_text(json.dumps(r,indent=1))
assert not r['present'],'Merged NMO candidate found: inspect/import read-only before gate; do not ignore it'
plan=json.loads((E/'NMP_FINAL_PLAN.json').read_text())
for i in plan['sequence']:
 a=f'NMP_L{i:03}';assert not(E/a/'receipt.json').exists(),('Never resubmit',a)
 rc=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 if rc.returncode:sys.exit(rc.returncode)
 if i==plan['regenerate_after']:
  assert subprocess.call([sys.executable,str(E/'NMP_prepare_audit.py')])==0
