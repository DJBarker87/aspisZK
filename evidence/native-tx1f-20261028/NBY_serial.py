from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for number in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NBY_K{number:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'NBY_host.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text())
 print(a,rc['exit_status'],flush=True)
 # On timeout, do not run an unchanged paired shape.
 if 'TIMEOUT' in (E/a/'stdout.log').read_text() or rc['exit_status'] in [124,137]:
  print('REVIEW timeout: stop series before any paired shape',flush=True);break
