from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
ats=[json.loads(l)for l in(E/'NJK_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(ats)==38 and ats[-1]['attempt']=='NJK_L038'and not(E/'NJK_CLIENT_ACTIVE').exists(),'Raw queue must finish before inspection/export'
for a,k,t in [('NJK_L039','lean','NJK_ContractInspection'),('NJK_L040','audit','close')]:
 r=subprocess.run([sys.executable,str(E/'NJK_run.py'),a,k,t],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(json.dumps(dict(attempt=a,exit=r.returncode,summary=r.stdout[-300:])),flush=True)
 if r.returncode:sys.exit(r.returncode)
r=subprocess.run([sys.executable,'-B',str(E/'NJK_finalize.py')],capture_output=True,text=True);(E/'NJK_FINALIZE.log').write_text(r.stdout+r.stderr);print(json.dumps(dict(stage='finalize',exit=r.returncode,summary=r.stdout[-600:],error=r.stderr[-700:])),flush=True);sys.exit(r.returncode)
