"""Owned sequential native queue; stop to diagnose any new timeout/compile failure."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
prerequisite=sys.argv[1]
while not (E/prerequisite/'receipt.json').exists():time.sleep(5)
assert json.loads((E/prerequisite/'receipt.json').read_text())['exit_status']==0
while (E/'NMP_CLIENT_ACTIVE').exists():time.sleep(1)
for spec in sys.argv[2:]:
 a,expected=spec.split(':');assert expected in ['pass','fail']
 assert not (E/a/'receipt.json').exists(),('Never resubmit',a)
 r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 timed='timed out' in out.lower() or rc['exit_status']==124
 compiled='could not compile' not in out and 'Traceback' not in out
 intended=(expected=='pass' and r.returncode==0) or (expected=='fail' and r.returncode!=0 and 'Failed Checks:' in out and 'VERIFICATION:- FAILED' in out and ('assertion failed' in out or ('** 1 of 31 failed' in out and 'core::panicking::assert_failed_inner' in out and a=='NMP_K008')))
 with (E/'NMP_VERDICTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=expected,exit=rc['exit_status'],timed_out=timed,compiled=compiled,intended=intended))+'\n')
 if timed or not compiled or not intended:sys.exit(1)
