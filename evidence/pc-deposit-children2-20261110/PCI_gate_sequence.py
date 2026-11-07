"""Fail closed, except the explicitly ruled raw/collector disagreement route."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for a in sys.argv[1:]:
 p=subprocess.run([sys.executable,str(E/'PCI_run.py'),a])
 r=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert r['exit_status'] not in [124,137] and 'timed out' not in out.lower()
 task=json.loads((E/'PCI_TASKS.json').read_text())[a]
 if task.get('raw_expected'):
  rows=[json.loads(s[11:]) for s in out.splitlines() if s.startswith('NEP_RESULT ')]
  assert [s['root'] for s in rows]==task['raw_expected']
  assert all(set(s['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for s in rows)
  assert r['exit_status'] in [0,1]
 else:assert p.returncode==0 and r['exit_status']==0,a
 print(a+' gate stage verified',flush=True)
