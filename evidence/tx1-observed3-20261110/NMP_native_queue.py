"""Owned sequential native queue; stop to diagnose any new timeout/compile failure."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
prerequisite=sys.argv[1]
prereq_negative=prerequisite.endswith(':fail')
if prereq_negative:prerequisite=prerequisite[:-5]
while not (E/prerequisite/'receipt.json').exists():time.sleep(5)
if prereq_negative:
 while True:
  verdicts=[json.loads(l) for l in (E/'NMP_VERDICTS.jsonl').read_text().splitlines()]
  found=[x for x in verdicts if x['attempt']==prerequisite]
  if found:
   assert found[-1]['intended'],found[-1];break
  time.sleep(1)
else:assert json.loads((E/prerequisite/'receipt.json').read_text())['exit_status']==0
while (E/'NMP_CLIENT_ACTIVE').exists():time.sleep(1)
for spec in sys.argv[2:]:
 a,expected=spec.split(':');assert expected in ['pass','fail']
 assert not (E/a/'receipt.json').exists(),('Never resubmit',a)
 r=subprocess.run([sys.executable,str(E/'NMP_run.py'),a])
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 timed='timed out' in out.lower() or rc['exit_status']==124
 contract_failure=('** 1 of ' in out and (( 'Failed Checks: |_| dst[probe]!=word' in out and 'NMP_havoc::inverse::' in out) or ('Failed Checks: Check that *var_' in out and ' is assignable' in out and 'NMP_havoc::bad_modifies::' in out)))
 compiled='could not compile' not in out and 'Traceback' not in out
 intended=(expected=='pass' and r.returncode==0) or (expected=='fail' and r.returncode!=0 and 'Failed Checks:' in out and 'VERIFICATION:- FAILED' in out and ('assertion failed' in out or contract_failure or (a=='NMP_K069' and 'Failed Checks: Check that *var_12 is assignable' in out and '** 1 of 106 failed' in out) or (a=='NMP_K065' and 'Failed Checks: |_| dst[probe]!=word' in out and '** 1 of 117 failed' in out) or ('** 1 of 31 failed' in out and 'core::panicking::assert_failed_inner' in out and a in ['NMP_K008','NMP_K100'])))
 with (E/'NMP_VERDICTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=expected,exit=rc['exit_status'],timed_out=timed,compiled=compiled,intended=intended))+'\n')
 if timed or not compiled or not intended:sys.exit(1)
