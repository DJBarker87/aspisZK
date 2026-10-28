from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NBJ_K{n:03}'
 assert not (E/a/'receipt.json').exists(),a
 r=subprocess.run([sys.executable,str(E/'NBJ_host.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
 d=json.loads((E/a/'receipt.json').read_text())
 print('TERMINAL',a,d['exit_status'],flush=True)
 if d['exit_status']!=0:raise SystemExit('Split failed shape before another native launch')
