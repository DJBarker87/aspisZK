from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
skip=False
for n in range(16,33):
 if n%2 and skip:skip=False
 if n%2==0 and skip:
  print(f'NJX_K{n:03}: not launched; isolate preceding timed-out/killed shape',flush=True);continue
 a=f'NJX_K{n:03}'
 r=subprocess.run([sys.executable,str(E/'NJX_run.py'),a])
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError('Missing receipt: recover read-only before any further launch')
 rc=json.loads(p.read_text())
 if n%2 and (rc['exit_status'] in [124,137,143] or 'TIMEOUT' in (E/a/'stdout.log').read_text()):skip=True
