"""Admission retries without spending a Lean ID; all scopes remain in lean.py."""
from pathlib import Path
import subprocess,time,json,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028'
a=json.loads((E/'43798-upload-admission.json').read_text());ready=datetime.datetime.fromisoformat(a['utc']).timestamp()+180
while time.time()<ready:time.sleep(min(15,ready-time.time()))
for i in range(10):
 label=f'audit-precheck-{i}'
 r=subprocess.run(['python3',str(R/'tools/pv-relink-20261028/upload.py'),label])
 if r.returncode==0:print('AUDIT ADMISSION READY',flush=True);break
 a=json.loads((E/f'upload-{label}.json').read_text())
 if a.get('allowed') is True:raise SystemExit(r.returncode)
 print('AUDIT WAIT',i,a.get('utc'),a.get('bounded_reserved_bytes'),flush=True)
 for _ in range(12):time.sleep(15)
else:raise SystemExit(78)
