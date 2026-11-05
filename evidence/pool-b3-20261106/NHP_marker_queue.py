from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i,(case,mode) in enumerate((c,m) for c in ['privilegesbusy','programborrow','programlength','systemempty','systemshared','systemnonempty','foreignbusy'] for m in ['positive','negative']):
 a='NHP_K'+str(72+i).zfill(3)
 g=subprocess.run([sys.executable,str(E/'NHP_marker.py'),mode,case],capture_output=True,text=True);assert g.returncode==0,g.stderr
 r=subprocess.run([sys.executable,str(E/'NHP_kani_run.py'),a,g.stdout.strip()],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text();okay=rc['exit_status']==(0 if mode=='positive' else 1) and ('VERIFICATION:- SUCCESSFUL' if mode=='positive' else 'VERIFICATION:- FAILED') in out and 'CBMC timed out.' not in out
 print(json.dumps(dict(attempt=a,case=case,mode=mode,exit=rc['exit_status'],expected=okay)),flush=True)
 if not okay:sys.exit(2)
