from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);names=sys.argv[2:]
for name in names:
 a=f'SDY_L{n:03}';m='SDY_'+name
 r=subprocess.run(['python3',str(E/'SDY_attempt.py'),a,str(E/(m+'.lean')),m])
 if r.returncode or json.loads((E/a/'receipt.json').read_text())['exit_status']:raise SystemExit(a+' failed')
 n+=1
