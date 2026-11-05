"""Checked serial generator/launch queue; no stale-input continuation."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;start=int(sys.argv[1]);generator=sys.argv[2];cases=sys.argv[3:]
for i,(case,mode) in enumerate((c,m) for c in cases for m in ['positive','negative']):
 a='NHP_K'+str(start+i).zfill(3);assert not (E/a).exists()
 g=subprocess.run([sys.executable,str(E/generator),mode,case],capture_output=True,text=True);assert g.returncode==0,g.stderr
 r=subprocess.run([sys.executable,str(E/'NHP_kani_run.py'),a,g.stdout.strip().splitlines()[-1]],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text();expected=rc['exit_status']==(0 if mode=='positive' else 1) and ('VERIFICATION:- SUCCESSFUL' if mode=='positive' else 'VERIFICATION:- FAILED') in out and 'CBMC timed out.' not in out
 print(json.dumps(dict(attempt=a,case=case,mode=mode,exit=rc['exit_status'],expected=expected)),flush=True)
 if not expected:sys.exit(2)
