"""Prescribed pre-upload resource check, before allocating any env-J ID.
The actual runner still performs both existing admission checks and uses the
unchanged scope caps. No launcher/shared infrastructure is edited.
"""
from pathlib import Path
import subprocess,json,time,shlex,sys
E=Path('evidence/pv-batch2-20261027/batch2f/admission-probes');E.mkdir(exist_ok=True)
label='batch2f-pre-submission-'+str(time.time_ns())
code='''from pathlib import Path
import subprocess,json,sys
D=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');O=D/'candidate'/LABEL;O.mkdir()
with (O/'reservation.log').open('w') as f:r=subprocess.run(['python3',str(D/'reservation.py'),str(O/'reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((O/'reservation.json').read_text()) if (O/'reservation.json').exists() else None
print(json.dumps(dict(label=LABEL,env_j_id=None,compiler_launched=False,exit=r.returncode,reservation=a,log=(O/'reservation.log').read_text())))
sys.exit(0 if r.returncode==0 and a and a.get('allowed') is True else 78)
'''.replace('LABEL',repr(label))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/(label+'.json')).write_text(r.stdout or json.dumps(dict(exit=r.returncode,stderr=r.stderr,env_j_id=None,compiler_launched=False)))
if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
print('pre-submission resource check admitted; no env-J ID allocated')
